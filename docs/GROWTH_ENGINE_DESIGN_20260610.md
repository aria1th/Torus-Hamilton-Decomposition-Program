# Growth-engine design for the final two holes — H5 (`assume_oddHighModulus`) + H6′ (`assume_oddLowClosure`) (2026-06-10)

Authoritative paper: the REWRITTEN manuscript
`/data/angel/repos/etc/even_modulus_rewrite_20260610/` (main tex §9 +
`subtex/coforest_splice_algebra.tex`, `anchor_schedule_spec.tex`,
`high_even_chain_datum.tex`, `high_even_growth.tex`,
`final_induction_framework.tex`, appendices `D5/D7_anchor_tables`,
`high_even_anchor_placement`, `high_even_verification_lemmas`).

Holes (in `EvenV11/Main.lean:457,468`):

* **H5** `assume_oddHighModulus : FinalOddHighModulusTargetPromotion` —
  for odd `d ≥ 5`, even `m` in range, `d < m`, certificate inputs →
  `FinalMarkedTarget d m` (= `Shared.TorusHamiltonDecomposition d m`,
  `FinalTargetPredicateBridge.lean:9` — an ACTUAL decomposition, not a Prop
  shell).
* **H6′** `assume_oddLowClosure : OddLowClosureBridge.OddLowClosure` — two
  fields (`EvenV11/V28Hard/OddLowClosureBridge.lean:38`):
  `chainPropagation : 9 ≤ d → odd d → m ∈ {4,6} → FinalMarkedTarget 7 m →
  FinalMarkedTarget d m` and
  `modulusFreeRestart : FinalOddHighModulusTargetPromotion → … even 8 ≤ m ≤ d
  → FinalMarkedTarget d m`.

**Architectural headline.** Because `FinalMarkedTarget` is the bare
decomposition, the H6′ field inputs are *unusable as data* (a
`Nonempty (CayleyDecomposition 7 m)` carries no chain fields; E6a showed only
the abstract cycle is extractable). Both holes must therefore be served by one
internal **constructive growth engine** producing a chain-data-carrying
witness type `HEDWitness d m` (Lean `Type`, §3 G2), with the bare targets
projected at the end. The H6′ field signatures are satisfied by *ignoring*
their `FinalMarkedTarget` arguments. The paper's restart packaging
(`D₀ = m − 1`) collapses in Lean: since growth is modulus-free
(`lem:growth-modulus-free`) and the D7 anchor covers every even `m > 7`,
ONE master theorem

> for every odd `d ≥ 7` and even `m ≥ 4`: `HEDWitness d m`
> (bases: D7 anchor for `m ≥ 8`, pointwise certificates for `m ∈ {4,6}`;
> then chained `7→9` + paired growth, no `m`-vs-`D` comparison)

plus the D5 anchor (`RHD(5,m)`, `m > 5`) discharges H5, the restart, and the
chain propagation simultaneously.

---

## Part 1 — Exact-criterion feasibility check (the de-risk gate)

The exact RF2 criterion (machine form:
`EvenV11/V28Hard/EndpointRowSchedule.lean` — a layer substituting `σ` for `ρ`
on support `U` is per-color bijective ⟺
`U + (stepVec (σ c) − stepVec (ρ c)) = U` per moved color) was applied to
every realization-level claim. **No wall was found.** One genuinely new
machine-checked constraint (parity, §1.1.c) was discovered that the paper
leaves implicit; it *explains* the paper's support-rank countdown rather than
contradicting it. A reconstruction script was built
(`scripts/reconstruct_high_even_anchor_schedules.py`, plus search harnesses);
its verdicts are cited below as [script].

### 1.1 Anchor schedules (§8 anchor_schedule_spec + §9) — grade: NEEDS-PROOF-BUT-FEASIBLE

**Substitution inventory** (from `def:anchor-schedule-realization`, the
placement appendix, and the rewrite's companion verifier
`certificates/scripts/verify_rank7_rootflat_certificates.py`, whose seed
format pins the conventions — base row at height `t` with shift `s` is the
CONSTANT chronological row `c ↦ (c+s) % D`; a stage substitutes the shifted
stage row `σ_r` on a support):

1. *Skeleton rows* — constant permutation rows. RF2-free
   (`layerMap_bijective_of_constant`). VERIFIED-BY-CONSTRUCTION.
2. *Pair-row splices* — two-color swaps `(p q)` of direction reads on
   supports closed under `±(stepVec q − stepVec p)`. Exactly
   `layerMap_bijective_of_swap_cylinder`. VERIFIED-BY-CONSTRUCTION.
3. *Triple-row splices* — the oriented 3-cycle is read as TWO rank-one
   substeps (paper: "a triple row gives two rank-one substeps", App. B). Two
   layer realizations are exact-criterion legal:
   (a) the full 3-cycle substituted on a support closed under its rank-2
   active plane (all three difference vectors lie in
   `⟨α_e1, α_e2⟩`) — a 2-valued-per-color substitution, safe; or
   (b) the two transpositions on two separate supports, each closed under its
   own swap direction — then the shared label's color is moved on BOTH
   supports (a ≥3-valued layer map), but with pairwise-disjoint supports each
   invariant under its own difference vector this factors into disjoint
   bijections — **this is NOT the H2 trap** (the trap was supports *not*
   individually invariant). It needs one new mechanical Lean lemma
   (multi-cylinder, G1). [script: ~500k schedules over both shapes, zero RF2
   failures.]
4. *Terminal triple `(t,0,1)`* — NOT a splice substitution: it is the
   terminal A2 carrier, realized by the t-dependent terminal block (H1
   machinery, `TerminalA2*`). The naive constant-row reading is refuted (the
   H1 audit's `terminalDir_m4_plainChart_not_rowLatin` precedent); the anchor
   realization must embed the terminal-block schedule on the three carrier
   labels.
5. **No full-row substitutions on proper supports anywhere** (W2 avoided);
   no color-sharing ribbon family beyond (3b), which is the safe disjoint
   form.

**Per-period displacement budget (closing columns)** — VERIFIED [script].
With base rows `c ↦ c + s_t`, color `c` crosses its isolated-label class
`ι_c` exactly `#{t : s_t ≡ ι_c − c (mod D)}` times per period; splice
corrections never touch `ι_c` (every forest edge avoids the isolate). For D5
the stage shifts `{0,1,2}` miss the needed classes `{ι_c − c} = {3,4}`; for
D7 shifts `{0,1,2,3,5}` miss `{4,6}`. Placing exactly ONE unused height in
each missing class (rest neutral) gives closing crossing count exactly `1`
for every color simultaneously — the unit carry `±1`, uniformly in `m`. This
needs two spare heights: `m ≥ D + 2` ⟺ even `m > D`, exactly the paper's
range — and machine-explains why `m = 4` is impossible for the D5 anchor.

**(c) NEW: the parity calculus** [script, the key reconnaissance finding].
For even `m`, `K = m^{D−1}` is even, so a single-`K`-cycle return is an ODD
permutation; constant rows are even; a cylinder substitution with difference
vector of order `m` on support `U` is odd ⟺ `|U|/m` is odd ⟺ (for even `m`)
`U` is a LINE (`m` points). Hence **each color needs an odd number of
line-support substituted layers**. Hyperplane-only placements plateau at
exactly `[2,2,2,2,2]` cycles (parity floor, observed across 8 independent
hill-climb seeds at `m = 6`); line-only placements merge-starve
(`[~196,…]`). The paper's support-size countdown `|M_{r,P}| = D − r − 1`
(support cosets of rank `D−r−1`: `m³, m², m` for D5) is precisely a
parity-correct mixed tower (one odd line layer per color at the last stage).
This is the same phenomenon as WILDE_SEARCH §1's parity calculus for H1b —
now identified as load-bearing for the anchors too.

**Honest status of the numeric reconstruction.** RF1/RF2/forests/budget all
verify; RF3 did not yet close because the simplified model omits (i) the
rank-countdown support tower with per-color contracted-fiber freedom and
(ii) the terminal-A2 block realization of the final triple. Randomized search
over the simplified families is structurally blocked by parity (now
understood), not by an exact-criterion wall. **Gate before G6 Lean work:
finish the reconstruction with (i)+(ii) integrated** — this is mechanical now
that the two missing mechanisms are identified, but it is unfinished, and the
project rule (precise negative > wishful design) requires saying so: the
anchor RF3 realization is the one place where the printed ledger's point
semantics have not yet been machine-replayed end to end.

### 1.2 Four-point growth rows `σ_{s,δ} = (s a)(b c)` — grade: NEEDS-PROOF-BUT-FEASIBLE

* Two **color-disjoint** transpositions: `(s a)` (leaf) and `(b c)`
  (quotient direction). They may be substituted on a common
  plane-closed support (closed under both `e = u_s − u_a` and
  `g = u_b − u_c`) or on separate supports each closed under its own
  direction; both shapes pass the exact criterion (same analysis as 1.1.3;
  known-safe class). The leaf swap's support must be crossed once per old
  quotient period (one-point carry, `lem:four-point-one-point-carry`): a line
  in the leaf direction with exterior fibers pinned at the
  `lem:growth-leaf-fiber-room` values (`0,1` trace; `2` transported reserve;
  `3` new site — distinct for every even `m ≥ 4`, tight at `m = 4`).
  Parity ledger: line supports are odd — consistent with the new returns
  needing odd parity on the `m²`-fold larger state.
* The boundary-avoiding phase and the projection-kernel discharge are
  **already formalized and proven** (`_holds`):
  `EvenV11/ProjectionKernel.lean` (plane/line quotient,
  `projectionKernelCriterion_*`), `EvenV11/GuideLocality.lean` (the full
  Table `tab:growth-row-projection-data`: supports `[0,1,-1,-2]/[3,4,2,1]`,
  boundaries `{1,-1,-2}/{4,2,1}`, chained `{2,7,5}/{2,8}`, phases
  `ρ = 3,7` ordinary and `1,5` chained, `hD : 11 ≤ D` for ordinary), audited
  value-by-value against the paper (PAPER_NUMERIC_AUDIT §1 row H5).

### 1.3 Chained 7→9 and paired D−2→D — grade: NEEDS-PROOF-BUT-FEASIBLE (the delicate construction)

* What is substituted where: rows `(0 2)(7 5)` then `(1 2)(0 8)` (chained,
  `Z/9` chart) resp. `(0 1)(−1 −2)` then `(3 4)(2 1)` (ordinary, `Z/D`); the
  second chained row's old edge decomposes triangularly
  `u_0 − u_8 = e_0 + g_1`, and the triangular kernel is already formalized
  (`triangularKernelCoordinate/QuotientZero`, `_holds`).
* The two new coordinates' RF2: leaf-direction cylinder invariance —
  VERIFIED-BY-CONSTRUCTION shape (G1 descriptors).
* **Continuation subtlety (checked, design-relevant):** the naive
  block-diagonal extension ("new colors read their own leaf at every height,
  old schedule literally unchanged") FAILS RF3 for the new colors: a new
  color's return would be `m·e_leaf = 0` plus a measure-zero correction —
  near-identity, never a single cycle. So growth does NOT literally extend
  the old `dir`; the output schedule is rebuilt over the relabeled `D+2`
  chart (new labels `0,3` resp. `0,1` joining the cyclic skeleton), and the
  old system continues at the QUOTIENT level: the chain datum's row-indexed
  old spans are exactly the interface consumed
  (`lem:growth-old-generator-invariant`). This forces the
  certificate-grows / re-realize architecture of §3 (G2/G4/G6 share one
  realization pipeline) — the single most important Lean design decision in
  this document.

### 1.4 Chain propagation at m ∈ {4, 6} (§10) — grade: FEASIBLE; hybrid design settled

* Per-step obligations at fixed `m`: the window tables, boundary sets,
  kernels, carrier separation, and reserve-room values are finite and
  decidable per step — but the step is **parametric in D** (labels live in
  `Z/D`, `D` unbounded), so "finite-checkable per dimension" does not make
  the *induction* finite. The right hybrid: **finite certificates at the
  bases only** (`HED(7,4)`, `HED(7,6)` — `native_decide` chain-field audits
  over the shipped pointwise `dir` witnesses, mirroring
  `certificates/scripts/check_hed_clauses.py`), **parametric step theorem**
  with per-step `decide`-able side conditions (the GuideLocality tables are
  already stated parametrically with `hD : 11 ≤ D`). The parametric content
  is exactly: the `HEDWitness` invariant + the two step theorems + the
  `Nat.le_induction` driver — nothing else.
* `m` enters only through: `IsUnit (±1 : ZMod m)` (all `m`), the leaf-fiber
  room values (`m ≥ 4`), and `NeZero` instances. Confirms
  `lem:growth-modulus-free` at Lean granularity.

### 1.5 Modulus-free restart — grade: VERIFIED-BY-CONSTRUCTION (thin corollary)

Growth past `D = m` changes **no budget**: the six-center lemma uses only
`|W| ≥ 7` odd; the kernels are label-space statements; carries are `±1`
(units mod every `m`); reserve room needs `m ≥ 4`. In Lean the restart is a
wrapper: `m ≥ 8` even ⟹ `m > 7` ⟹ D7-anchor `HEDWitness 7 m` ⟹ propagate to
`d`. It does not even need the paper's `D₀ = m − 1` waypoint. It DOES need
the D7 anchor (G6) — it is a thin corollary of the H5 engine, as
anticipated.

**Part 1 conclusion: no STOP. One yellow flag** — the anchor RF3
point-semantics reconstruction is unfinished (1.1, with the two missing
mechanisms precisely identified and no exact-criterion violation anywhere).
Module G6 is gated on closing it numerically first.

---

## Part 2 — Lean inventory map (verified by reading)

Exists and consumable:

| asset | file | role here |
|---|---|---|
| RF2 exact criterion, swap/const `LayerDesc` plans | `EvenV11/V28Hard/EndpointRowSchedule.lean` | G1 extends with multi-cylinder + plane descriptors |
| RF1/RF2/RF3 → decomposition | `Shared/RootFlat.lean`, `EvenV11/RootFlatCycleData.lean` (`RootFlatCycleData`, `finalRootFlatTorusCertificate_of_cycleData`) | the engine's output funnel (`n = d−1`) |
| growth-row tables, boundary phases ρ=3,7,1,5, old-generator centers | `EvenV11/GuideLocality.lean` (1956 ln, audited) | G4 consumes as-is |
| four-point + triangular kernels (`_holds`) | `EvenV11/ProjectionKernel.lean`, `EvenV11/HighEvenSuccessorBridge.lean` | G4 consumes as-is |
| splice calculus: `oneStepPacketSplice(_On)`, `flagSplicingCriterion`, certificates | `Shared/SwitchCalculus.lean` | G6 RF3 tower; G4 quotient joins |
| unit carry, point carry, rank-unit lift | `EvenV11/UnitCarry.lean`, `Shared/ReturnLift.lean` | G4/G6 lifts |
| `rankEquiv` of a single cycle (converse) | `EvenV11/V28Hard/CompletionTower.lean` | normal forms of old returns inside `HEDWitness` |
| parent-cycle extraction | `EvenV11/V28Hard/EndpointParentCycle.lean` | precedent only (shows bare targets yield no schedule — justifies ignoring H6′'s inputs) |
| type-A coforest audits (D5 full, D7 stages 1–2), `v28FiniteInputCoforestAudit` | `EvenV11/TypeA/{TreeIncidence,CoforestExample,AnchorBridge}.lean` | G6 quotient certificates — **D7 stages 3–5 (18 rows) still unported** (audit §3's trap: the name sounds total) |
| closing-column unimodularity (R1), support ranks, reserve planes, JSON audits | `EvenV11/D5D7SeedTables.lean`, `FiniteAudit(Bridge).lean` | G6 unit-carry input |
| terminal A2 block (m² carrier cyclicity, t-dependent rows) | `TerminalA2LowMod`, `V28Hard/D3TerminalA2*`, `TerminalFiniteCyclicity` | G6 terminal carrier realization (1.1.4) |
| rail-seam wild-layer grammar | `V28Hard/D3EvenRail*` | reserve option if anchor splice lines need zigzag attachments (WILDE_SEARCH §5 suggested it for lane attachments); not in the primary plan |
| H3/H4 pointwise witnesses (`dir` on `Fin 4096`/`Fin 46656`, native_decide RF1–3) | `EvenV11/LowD7M4Finite.lean`, `LowD7M6Finite.lean` | G3 base schedules |
| engine input/output records | `FinalTargetHighEvenCertificateBridge.lean` (`FinalOddHighModulusCertificateInputs`, `…TargetPromotion`), `V28Hard/OddLowClosureBridge.lean` | G7 |

**Update of PAPER_NUMERIC_AUDIT_20260609.md §3 against the rewrite:**

* *Died with the rewrite*: the endpoint-successor consumers of H5's marked
  payload (the E6 walls analysis stays valid as errata, but nothing on the
  new spine consumes it); audit risk ④ — `ManuscriptHardSectionData.
  finiteCoforestAnchor` demanding anchors for ALL odd `D ≥ 5` — the rewrite
  restricts anchors to `D ∈ {5,7}` + growth, so that interface shape should
  not be ported; the old `prop:seed-realization` naming (absorbed into
  `def:anchor-schedule-realization`/`prop:anchor-schedule-realization`).
* *Remain (and are scheduled below)*: stage-skeleton → forest derivation
  theorem; Latin-skeleton check; D7 stage 3–5 contracted coforests; R3
  ledger (old-head transversals 12+32 cells, tail–head identities, now
  per-color via eq. (B.1)); D5/D7 terminal alignment; reserve
  projection-separation (now `lem:affine-reserve-plane`); `RHD/HED`
  predicates (no Lean def yet — becomes `HEDWitness`); splice composition
  (exists); quotient-to-layer lift (`lem:quotient-to-layer-support-lift` —
  new); growth propositions + closure corollaries; reserve transport; risk ⑤
  (engine must internalize the induction) — adopted as the headline
  architecture.
* *New items the audit did not list*: the parity calculus (1.1.c) as an
  explicit proof obligation/design guard; the terminal-A2-block embedding
  into anchor schedules (1.1.4); the non-extension of `dir` under growth
  (1.3) forcing the certificate-grows architecture.

---

## Part 3 — Module decomposition

Output funnel for everything: `RootFlatCycleData (d−1) m` →
`finalRootFlatTorusCertificate_of_cycleData` → `FinalMarkedTarget d m`.

### G1 — `EvenV11/HighEven/GrowthRowSchedule.lean` (mechanical, ~350 ln)

Multi-cylinder RF2 + four-point descriptors, extending
`EndpointRowSchedule`.

```lean
/-- Disjoint family of cylinders, each with its own two-color swap; every
support invariant under its own difference vector. -/
theorem layerMap_bijective_of_disjoint_swap_family {n m : Nat} [NeZero m]
    (rowAt : ZMod m → RootState n m → Equiv.Perm (Fin (n+1))) (t : ZMod m)
    (ρ : Equiv.Perm (Fin (n+1))) (k : Nat)
    (α β : Fin k → Fin (n+1)) (U : Fin k → Set (RootState n m))
    (hdisj : Pairwise (Function.onFun Disjoint U))
    (hoff : ∀ w, (∀ i, w ∉ U i) → rowAt t w = ρ)
    (hon : ∀ i, ∀ w ∈ U i, rowAt t w = ρ.trans (Equiv.swap (α i) (β i)))
    (hinv : ∀ i w, w ∈ U i ↔ (w + (stepVec (β i) - stepVec (α i))) ∈ U i) :
    ∀ c, Function.Bijective ((rowSchedule rowAt).layerMap t c)

inductive LayerDesc' (n m : Nat)   -- extends LayerDesc
  | const …
  | swapFamily (ρ : Equiv.Perm (Fin (n+1))) (k : Nat)
      (α β : Fin k → Fin (n+1)) (U : Fin k → Set (RootState n m))

/-- four-point growth row descriptor: the two disjoint transpositions
(s a)(b c) of σ_{s,δ} as a 2-member swap family. -/
def fourPointDesc … : LayerDesc' n m
```

Also (optional, recommended as design guard): the parity lemma

```lean
theorem cylinderShift_parity {…} (hinv …) (hcard : Nat.card U = m * k) :
    Equiv.Perm.sign (cylinderShiftPerm U d hinv) = (-1)^k
theorem singleCycle_return_parity_even_m …  -- single m^n-cycle is odd
```

Verification anchors: `decide` at `n=4, m=4` for descriptor instances;
cross-validate against the script's RF2 logs.

### G2 — `EvenV11/HighEven/ChainDatum.lean` (structure design: delicate; proofs mechanical)

The Lean `HED(D,m)` — a `Type`, certificate-level (per 1.3 the schedule is
re-realized each dimension, so the witness carries the QUOTIENT certificate
plus the current realized schedule):

```lean
structure HEDWitness (D m : Nat) [NeZero m] where
  hD   : 7 ≤ D       hodd : D % 2 = 1       hm : 4 ≤ m       hev : Even m
  -- realized layer schedule (current dimension)
  cycleData : RootFlatCycle.RootFlatCycleData (D - 1) m
  -- chain fields (def:high-even-chain-datum, in the OUTPUT chart of the
  -- next growth step, i.e. Z/(D+2) with new labels {0,3} resp. Z/9 \ {0,1})
  oldGens   : GrowthRowIdx → List (ZMod (D + 2) × ZMod (D + 2))  -- 𝒢⁻_r
  oldGensSpec : … -- the displayed-interface equations of
                  -- lem:growth-old-generator-invariant for these lists
  carrier   : Fin 3 → ZMod (D + 2)        -- separated terminal A₂ carrier
  carrierSep : …                          -- disjoint from row supports
  reserve   : ReserveForm D m             -- fixed-fiber reserve (D+3 sites)
  quotient  : ColorQuotientCert D m cycleData
  -- per color: rankEquiv normal form of the return + the row-indexed
  -- inactive-flag data the next step's projection-kernel discharge needs
```

plus `HEDWitness.toMarkedTarget : HEDWitness D m → FinalMarkedTarget D m`
(forgetful, `lem:chain-datum-forgetful`). Minimality rule: a field enters
only if G4 consumes it; start from the six items of
`def:high-even-chain-datum` and prune during G4.

Verification anchors: instantiate every field at `(7,4)` from the shipped
JSON data; `decide` the chart/carrier arithmetic (`Z/9 \ {0,1}`, `{3,4,6}`)
as in `check_hed_clauses.py`.

### G3 — `EvenV11/HighEven/LowModulusChainBases.lean` (mechanical + `native_decide`, ~400 ln)

`hed74 : HEDWitness 7 4`, `hed76 : HEDWitness 7 6` over the H3/H4 `dir`
witnesses (`LowD7M4Finite`/`LowD7M6Finite`). Chain fields are read off the
reconstructed returns by `native_decide` audits transcribing
`check_hed_clauses.py` (fixed-fiber reserve `(y; m−1,m−1; 0,0)`, carrier,
seven-site ledger → `oldGens` lists, protected-neighborhood separation).
This is paper `thm:low-modulus-input-instantiated` +
`prop:rank-three-chain-bases`. Dependencies: G2.

### G4 — `EvenV11/HighEven/GrowthStep.lean` (THE ENGINE; delicate) 

```lean
theorem chainedGrowth  {m : Nat} [NeZero m] (hm : Even m) (h4 : 4 ≤ m) :
    HEDWitness 7 m → HEDWitness 9 m                       -- prop:chained-two-hole
theorem pairedGrowth   {D m : Nat} [NeZero m] (hD : 9 ≤ D) (hodd : D % 2 = 1)
    (hm : Even m) (h4 : 4 ≤ m) :
    HEDWitness D m → HEDWitness (D + 2) m                 -- prop:paired-growth
```

Construction per step: rebuild the `(D+1)`-coordinate schedule over the
relabeled chart (1.3): skeleton from the input's `cycleData` conjugated by
the chart embedding + the two four-point rows (G1 descriptors) at
boundary-avoiding phases (`GuideLocality` choices `ρ = 3,7` / `1,5`); leaf
supports = lines in the leaf directions, exterior fibers pinned at the
`growth-leaf-fiber-room` values; per-color RF3 by: projection-kernel
discharge (`ProjectionKernel` + `GuideLocality`, `_holds` — old span dies in
`P/L`), `oneStepPacketSplice` joins, one-point carry
(`UnitCarry.pointCarry` + `rankUnitCarrySingleCycle`, carries `±1`), with
the input's `quotient`/`rankEquiv` normal forms as the old-system interface;
reserve transport per `lem:growth-reserve-transport` (values `2`,`3` in the
leaf fibers). Dependencies: G1, G2; consumes G3/G6 outputs.

Verification anchors (do BEFORE the Lean proofs): extend the reconstruction
script with a `grow` function and replay `7→9` at `m = 4` on the shipped
`D7_m4_seed.json` (`K = 4^8` per color — feasible with arrays), then `9→11`;
this is the growth-engine analogue of the anchor reconstruction and the
template for the Lean witness format.

### G5 — `EvenV11/HighEven/ChainPropagation.lean` (mechanical, ~150 ln)

```lean
theorem chainClosure {m : Nat} [NeZero m] (hm : Even m) (h4 : 4 ≤ m)
    {d : Nat} (hd : 7 ≤ d) (hodd : d % 2 = 1) :
    HEDWitness 7 m → HEDWitness d m          -- cor:odd-chain-propagation
```

Two-step `Nat.le_induction`; first step chained, rest paired. No `m`-vs-`D`
hypothesis anywhere (`lem:growth-modulus-free` holds by inspection of
G4's signature). Discharges H6′.`chainPropagation` via G3 + `toMarkedTarget`
(ignoring the bare-target argument). Dependencies: G4, G3.

### G6 — `EvenV11/HighEven/AnchorScheduleD5.lean`, `AnchorScheduleD7.lean` (**hardest**) 

```lean
theorem d5AnchorRHD {m : Nat} [NeZero m] (hm : Even m) (h5 : 5 < m) :
    RootFlatCycle.RootFlatCycleData 4 m          -- RHD(5,m) realized
theorem d7AnchorHED {m : Nat} [NeZero m] (hm : Even m) (h7 : 7 < m) :
    HEDWitness 7 m                               -- thm:finite-anchors
```

Content (per 1.1): shift multiset (stages + one height per missing class,
budget lemma); splice units on rank-countdown supports (G1 descriptors:
plane/line tower, parity-correct); terminal A2 block embedded on the carrier
labels (consume `TerminalA2*`); RF3 = `flagSplicingCriterion` over the
laminar per-color flags (TypeA coforest audits — **port D7 stages 3–5
first**), old-head transversality (`lem:support-line-transversal` — new,
mechanical from `TreeIncidence`), tail–head identities (eq. (B.1) —
`decide` per stage), closing lift (`D5D7SeedTables` determinants +
`UnitCarry`/`lem:anchor-unit-carry-lift`), reserve plane
(`lem:affine-reserve-plane` over `AffineSeparation`/
`EndpointReservePlacement` patterns).
Dependencies: G1, G2, TypeA, D5D7SeedTables, TerminalA2.
**Gate: the numeric reconstruction (1.1) must first produce one verified
`m = 6` (D5) and `m = 8` (D7) schedule with the tower+terminal mechanisms;
its placement data then becomes the Lean witness constants.**

### G7 — `EvenV11/HighEven/HighEvenEngine.lean` (mechanical, ~200 ln)

```lean
theorem oddHighModulusEngine : FinalOddHighModulusTargetPromotion
  -- d = 5: G6-D5; d = 7: G6-D7.toMarkedTarget; d ≥ 9: G5 (G6-D7)
theorem oddLowClosure : V28Hard.OddLowClosureBridge.OddLowClosure
  -- chainPropagation: fun _ => (G5 (G3 m)).toMarkedTarget
  -- modulusFreeRestart: fun _ … h8 _ => (G5 (G6-D7, m > 7 from h8)).toMarkedTarget
```

Then `Main.lean:457/468` close. The `FinalOddHighModulusCertificateInputs`
argument is consumed for its audit booleans only (they are `_holds` anyway).

### G8 (optional) — `EvenV11/HighEven/ParityGuard.lean`

The 1.1.c parity lemma as a machine-checked negative guard (the analogue of
H2's `not_terminalCoreTailPrefixPathGoal` and E6-W2): *for even `m`, any
plan whose substituted supports all have even index leaves every return an
even permutation, hence never a single cycle.* Low priority; documents why
the support countdown is forced.

### Order and the hardest item

```
G1 → G2 → G3 ┐
             ├→ G4 → G5 ──→ (H6′.chainPropagation lands here, anchor-free)
G1 → G6 ─────┘        └──→ G7 (needs G6 for H5 + restart)
```

**Single hardest item: G6, the anchor schedule realization (RF3)** — it is
the one module whose paper ledger has not yet been machine-replayed
(Part 1.1 yellow flag), it needs the splice tower + terminal-A2 embedding +
parity-correct placements simultaneously, and both H5 and
H6′.`modulusFreeRestart` are gated on its D7 half. G4 is a close second
(parametric in both `D` and `m`) but every analytic ingredient it needs is
already formalized (`_holds`) and its numeric replay is straightforward.
Recommended attack order: finish the G6 numeric reconstruction (script,
tower+terminal), land G1–G5 meanwhile (closes `chainPropagation`, the larger
half of H6′), then G6/G7.

---

## Appendix — reconnaissance artifacts

* `scripts/reconstruct_high_even_anchor_schedules.py` (this repo): D5/D7
  anchor reconstruction harness mirroring the rewrite verifier conventions.
  Verified PASS: RF1, RF2 (all placements, both triple shapes), one-isolate
  forests, closing-column unit budget at `m = 6, 8` (and its impossibility
  at `m = 4` — matching the paper range `m > D`). RF3: PARTIAL (documented
  in the docstring; parity floor `[2,2,2,2,2]` and merge starvation
  `[~196,…]` machine-observed; missing mechanisms identified as the
  rank-countdown tower + terminal-A2 block).
* Search harnesses (session-local `/tmp/d5_search*.py`, reproducible from
  the script's building blocks): ~500k schedules checked; zero RF2
  failures; best RF3 cycle counts `[2,2,2,4,1]` (m=4 truncated model) and
  `[2,2,2,2,2]` (m=6, the parity floor).
* Conventions source: `even_modulus_rewrite_20260610/certificates/scripts/
  verify_rank7_rootflat_certificates.py` (seed format: `layer_shifts`,
  `stages` with `sigma`+`supports`, `local_table` wild layers,
  `layer_overrides`) and `check_hed_clauses.py` (chain-field clause checks —
  the template for G3's `native_decide` audits).
