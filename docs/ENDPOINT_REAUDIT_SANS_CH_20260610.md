# Endpoint section re-audit (C_h route excluded) — exact two-valued RF2 criterion (2026-06-10)

Context: the author has CONFIRMED (`QUESTION_W2_COMPLETION_FIBER_20260610.md`, header note)
that `lem:completion-fiber-bijectivity` (localizing the full cyclic row `C_h` on lifted
completion fibers; `endpoint_successor.tex:265-298` + the `C_h` rows of
`lem:endpoint-local-row-realization:300-335`) is wrong and will be revised.  This audit
re-checks every REMAINING realization-level claim of the endpoint section, and the two
HIGH-EVEN spot checks, against the exact criterion, so the paper revision and the
formalization both know what stands.

Paper source: `/tmp/v28_paper/even_modulus_directed_tori_v28_finite_audit_source/subtex/`
(`endpoint_successor.tex`, `switching_ribbons.tex`, `general_endpoint_port_room.tex`,
`endpoint_b4_chart.tex`, `D54_parity_reset.tex`, `high_even_seed_realization.tex`).
Lean criterion: `EvenV11/V28Hard/EndpointRowSchedule.lean` (esp.
`layerMap_bijective_of_cylinder` :170-193, `layerMap_bijective_of_swap_cylinder` :217-244,
`mem_iff_add_neg_mem` :63-69).  Chart indices: `EvenV11/V28Hard/EndpointChart.lean`
(`exchangeTauIdx` val = i, `exchangePlusIdx` val = 3+2i, `resetFirstIdx` val = 4 (p₁⁻),
`resetSecondIdx` val = 6 (p₂⁻); Lean kills `p_{b-1}⁻ = Fin.last`, paper chart Φ kills τ₀).

## 0. The exact criterion (recap, fixed notation)

Layer row = ρ off support U, σ on U.  Color-c layer map is the two-valued translation
`w ↦ w + v_{σ(c)} [w∈U] / w + v_{ρ(c)} [w∉U]` (v_ω = `stepVec` image of e_ω in the layer
chart).  Bijectivity for color c ⟺

> (★)  U + (v_{σ(c)} − v_{ρ(c)}) = U,

and failure of `U + d ⊆ U` produces an explicit collision pair
(w ∈ U, w' = w + d ∉ U ⇒ both map to w + v_{σ(c)}).  For a swap row
σ = ρ∘swap(α,β) only the two colors reading α/β move, with difference vectors
±(v_β − v_α); ONE invariance suffices (`layerMap_bijective_of_swap_cylinder`).
Chart-free formulation: U ⊆ L_t, condition U + (e_β − e_α) = U in the height-zero
sublattice.  The W2 failure: `C_h` moves EVERY color's read; the difference vectors
generate the whole lattice (gcd(h,2b+1)=1), so no proper nonempty U is invariant
(`E6_DESIGN_20260610.md` §4.2).

Throughout, E-coordinates: q = (x_{τ₁}, x_{τ₂}) (terminal state), y_j = x_{p_{j+1}⁺}
(parent/plus lanes), z_j = x_{p_{j+1}⁻} (minus lanes); x_{τ₀} is height slack.
KEY FACT used repeatedly: a layer-set pinning some coordinates is (★)-invariant for
difference vector d iff d's projection avoids every pinned coordinate; the systematic
RF2-legal family is supports free in the coordinates that the swap moves —
equivalently, swaps whose two directions both avoid the pinned block
(`E6_DESIGN_20260610.md` §1.2 "key cylinder fact").

## 1. Grade table

| # | Claim | Paper citation | Grade |
|---|---|---|---|
| 1a-i | `lem:partial-exchange` + `lem:layer-comparison-switch` are criterion-exact | switching_ribbons.tex:21-41, :43-53 | **VERIFIED** |
| 1a-ii | ribbon construction gives (★)-invariant U by construction | switching_ribbons.tex:55-68; endpoint_successor.tex:252-263, :327-330 | **VERIFIED** (as stated; residual obligations listed in §2.1) |
| 1a-iii | X₀ exchange ribbon `𝓡_{τ₀,p₁⁺}(S_{X₀})` realizes the t₀/d₁ ledger row | endpoint_successor.tex:74-78, :308, :315; ledger :33-34 | **PLAUSIBLE-NEEDS-PROOF** (support must be restated as the q-pinned cylinder; "one parent step = P_i" identification is Wall 1 / wild-e) |
| 1a-iv | X₁, X₂ exchange ribbons realize the t₁/d₂, t₂/d₃ ledger rows | endpoint_successor.tex:74-78, :308; port room :40, :88-91 | **SUSPECT-LIKE-W2** (provable (★)-violation: any support pinning the terminal state is moved by e_{p_{i+1}⁺} − e_{τ_i}, i = 1,2; the (★)-legal closure destroys the exponent-1 ledger) |
| 1b | R reset row on `𝓡_{p₁⁻,p₂⁻}(S_R)` with common image I | endpoint_successor.tex:309, :316-317, :337-361; port room :52-73, :91-96 | **PLAUSIBLE-NEEDS-PROOF** (RF2-exact on the m-point line closure; common image is cross-color hence criterion-safe; 2-site description must become an m-point statement) |
| 1c | `lem:switching-ribbons` (ribbon composition) is criterion-exact | switching_ribbons.tex:190-207 | **PLAUSIBLE-NEEDS-PROOF** in general (shared-color image collisions unaddressed); criterion-exact FOR COLOR-DISJOINT families, which the sans-C_h endpoint family is; the D5(4) §11 application is **SUSPECT-LIKE-W2** (empirically refuted naive reading, blocker §8) |
| 2a | return ledger `±1` carry / `lem:endpoint-completion` as abstract skew-product math | endpoint_successor.tex:25-40 (row :35), :125-178 | **VERIFIED** (abstract level; Lean `EndpointCompletion`/`CompletionTower` closed) — but its row-level ATTRIBUTION to `C_h` is the confirmed-wrong part |
| 2b | swap-based one-point carry replacement ((α, zero-direction) pairs) consistent with actual certificates | E6_DESIGN §4.2-4.3; QUESTION_W2 Q3; LowD5M4Finite.lean | **PLAUSIBLE-NEEDS-PROOF** (RF2-legality of single carries confirmed; donor/parity bookkeeping (Wall 3) and word budget (Wall 1) open; actual D5(4) certificate gives NO structural confirmation — see §2.4) |
| 3 | port-room separation sans C_h | general_endpoint_port_room.tex:37-45, :75-120 | **PLAUSIBLE-NEEDS-PROOF** (reset separations survive verbatim; exchange separations must migrate from parent projections to terminal-state pins; completion-fiber separations obsolete) |
| 4a | `lem:quotient-to-layer-support-lift` | high_even_seed_realization.tex:363-392 | **PLAUSIBLE-NEEDS-PROOF** (image-level mechanism is criterion-compatible, but the "separated" hypothesis is source-level and must be sharpened to head-line-vs-old-image disjointness) |
| 4b | `lem:one-step-packet-splice` | high_even_seed_realization.tex:467-494 | **VERIFIED** (purely return-level cut-splice; no RF2 content; realization deferral inherits 4a's obligations) |
| (aux) | `lem:endpoint-active-core` product-cycle math | endpoint_successor.tex:45-64, :66-111 | **VERIFIED** abstractly (Lean E6b-1/2 routes exist); realization graded under 1a-iii/iv |
| (aux) | `lem:endpoint-marked-transfer` | endpoint_successor.tex:337-361 | **PLAUSIBLE-NEEDS-PROOF** (must be restated for the m-point reset line and q-pinned exchange supports) |

## 2. Detailed analysis

### 2.1 Claim 1a — exchange rows X_i and the ribbon construction

**(i) The switching grammar is criterion-exact.**  `lem:partial-exchange`
(switching_ribbons.tex:21-41) states T_U, R_U bijective **iff** T⁻¹R(U) = U, and the
proof is the exact image computation `T((X∖U) ∪ T⁻¹R(U)) = X ⟺ U ⊆ T⁻¹R(U)` —
this IS the two-valued criterion in permutation form; with T, R the translations
+v_α, +v_β it is literally (★) (Lean `cylinderShift_bijective` is the translation
instance).  `lem:layer-comparison-switch` (:43-53) applies it with (T,R) = (g,f) for
one affected color; the other color's condition f⁻¹g(U) = U follows because a
permutation and its inverse have the same invariant sets — same content as Lean's
`mem_iff_add_neg_mem` reduction to ONE invariance.  RF1 is preserved because a
two-entry exchange keeps the row a permutation.  **VERIFIED**: these two lemmas have
no W2-style gap.

**(ii) The ribbon makes the invariance true by construction.**  The ribbon
`𝓡_{α,β}(S)` is generated as a union of alternating two-color components; per layer,
the alternating component intersected with L_t is a union of cycles of
F_{β,t}⁻¹F_{α,t} (`lem:ribbon-realization` :55-68; for endpoint layers with the
neutral base row, F_{β,t}⁻¹F_{α,t} is the translation by v_α − v_β, whose cycles are
the (v_α − v_β)-lines).  A union of cycles of a permutation is invariant under it, so
the per-layer RF2 identity `F⁻¹_{β,t}F_{α,t}(U_t) = U_t` (endpoint_successor.tex:256-263)
holds **by construction** for whatever seed S.  This reading is confirmed.  What it
does NOT give for free, i.e. what remains to prove:

1. **The closure must equal the support that the return ledger needs.**  The ribbon is
   the (v_α − v_β)-line closure of the seed.  The port room hands only SINGLETON sites
   x_i (:17-19, :88-91), but `lem:endpoint-active-core` (:74-78) needs the exchange to
   fire at terminal state q_i **for every (y,z)** — a fiber-sized support
   {q = q_i} × Y × Z, not one line of m points.  Neither the seed S_{X_i} nor the
   identity closure = intended support is ever stated; the paper computes the ledger
   from the template model and never computes the return effect of the actual closed
   ribbon.
2. **The closure must not leak into other rows' supports / N(C)** — see §2.5; note the
   X_i closure direction moves the PARENT coordinate y_i, so parent-projection-based
   separation (:84) is not automatically inherited by the closure.
3. The inserted read is **one unit step**; the ledger's inserted object is the full
   parent return P_i (an m^{b-1}-cycle).  The identification "one swapped read realizes
   one application of P_i" is the run-collapse/wild-e problem (Wall 1,
   `E6_DESIGN_20260610.md` §3.3, `H2_REALIZATION_BLOCKER_20260605.md` §1-2): per-period
   displacement of the firing branch exceeds the m-step budget under any LINEAR chart.
   This is orthogonal to RF2 but blocks a tame realization of the ledger even where
   RF2 is fine.

**(iii) X₀ is RF2-clean with the corrected support; X₁, X₂ are not.**  Chart-free
check.  The intended firing support pins the terminal state, i.e. pins the two
coordinates (x_{τ₁}, x_{τ₂}).

* X₀ = (τ₀ ↔ p₁⁺): difference vector e_{p₁⁺} − e_{τ₀} moves x_{p₁⁺} (= y₀) and the
  slack x_{τ₀} — **neither is pinned** by {q = q₀}.  So U = {q = q₀} × Y × Z satisfies
  (★), the swap fires exactly at terminal state q₀ on every (y,z), and the t₀/d₁
  ledger row (b4 chart, endpoint_b4_chart.tex:31-32) is shape-consistent: d₁ loses its
  y₀-step exactly at q₀, t₀ gains it.  Lean side: this is exactly the
  `exchangeDesc`/`layerMap_bijective_of_exchangeRow` shape with a legal cylinder
  (i = 0 difference = e₃ − e₀ in the Lean chart; pinned block = {w₁, w₂}; invariant ✓).
  Grade **PLAUSIBLE-NEEDS-PROOF**: support statement must be corrected
  (cylinder, not singleton; port-room parent factor U₀ is then NOT the support's
  parent projection — see §2.5), and the P_i identification is Wall 1.
* X₁ = (τ₁ ↔ p₂⁺), X₂ = (τ₂ ↔ p₃⁺): difference vector e_{p_{i+1}⁺} − e_{τ_i}
  **moves the pinned coordinate x_{τ_i}** (Lean: e_{3+2i} − e_i with i ∈ {1,2} = a
  q-coordinate).  Any support pinning the terminal state violates (★); the explicit
  collision pair is w ∈ U, w' = w + (e_{p⁺} − e_{τ_i}) ∉ U, both mapped by color t_i
  to w + e_{p⁺}.  Decide-able at b = 4, m = 4, same family as the W2 negative theorem.
  The (★)-legal repair — close under the line — sweeps the terminal coordinate:
  the closure of {q = q_i} is {q ∈ q_i + ℤ·e_{(i)}} (an m-line of terminal states),
  on which the exchange fires m times per terminal period, giving exponent sum m with
  gcd(m, M_i) = m ≠ 1 — `lem:product-cycle-exponent`'s unit check (:103-107) fails and
  the product return is NOT cyclic.  So as printed, X₁/X₂ cannot satisfy RF2 and the
  exponent-1 ledger simultaneously.  Grade **SUSPECT-LIKE-W2**.  This is the same
  failure mechanism as W2 (difference vector moves a coordinate the support must pin),
  restricted to one coordinate instead of all of them.  It is consistent with (and
  sharpens) `E6_DESIGN_20260610.md` §1.2's observation that the only systematic
  RF2-legal localized supports are those whose swap directions avoid the pinned block:
  X₀'s pair contains τ₀ (legal family); X₁/X₂'s pairs contain τ₁/τ₂ (illegal whenever
  the terminal state is pinned).  Note Wall 3 (§4.3) already records that repair
  attempts via τ₀-mediated 3-cycles re-violate the exact criterion; a genuine
  redesign (different firing condition, or a wild correspondence) is required.

### 2.2 Claim 1b — the reset row R

Swap pair (p₁⁻ ↔ p₂⁻), difference d = ε₂⁻ − ε₁⁻ (Lean e₆ − e₄): moves only minus
lanes z₀, z₁ — parent and terminal coordinates are FIXED along the closure.

* **The two reset sites lie on one comparison line.**  Port room
  (general_endpoint_port_room.tex:57-59) sets r₁ = r₀ + ε₁⁻ − ε₂⁻ = r₀ − d.  So the
  seed pair {r₀, r₁} is contained in the single d-line through r₀, and the ribbon
  `𝓡_{p₁⁻,p₂⁻}(S_R)` is that **m-point line** (the pair itself is NOT (★)-invariant
  for m ≥ 4; the closure is).  On the line, RF2 is exact: μ₁'s image of U is U + ε₂⁻,
  off-image is (complement) + ε₁⁻; a collision would force w = u + d ∈ U.  ✓
* **The common image is cross-color and the exact criterion accommodates it.**
  RF2 is per-color injectivity; the prescribed common head
  I = r₀ + ε₁⁻ = r₁ + ε₂⁻ (:63-64) is an image shared by the two DIFFERENT colors
  μ₁, μ₂, which never enters any per-color disjointness analysis.  Moreover the reset
  equation is robust to the switch: pre-swap, μ₁(r₀) = I and μ₂(r₁) = I; post-swap
  (both tails inside U), μ₂(r₀) = r₀ + ε₁⁻ = I and μ₁(r₁) = r₁ + ε₂⁻ = I — the swap
  merely exchanges which tail feeds which color into I.  So the common image does NOT
  live only at the abstract-return level; it is realized at the layer level either way.
  The paper should still say WHICH configuration (pre/post) carries the marked edge,
  since `lem:endpoint-reset-common-image`'s displayed equations describe neutral reads
  while `lem:endpoint-local-row-realization` swaps exactly those reads.
* **What needs restating**: (i) the localized support is the full m-point line, so the
  port-room phrase "the two reset supports are separated by their minus coordinates"
  (:93-95) and the table's "reset plane with one prescribed common image" (:134) are
  not the RF2-legal object — there is ONE support line containing both tails plus
  m − 2 bystander points; (ii) `lem:endpoint-marked-transfer` (:343-361) protects a
  2-point interaction with N(C); since the line lies over the selector point c_∗ — the
  same parent footprint as the lifted comparison cycle, by design — the
  "predecessor/successor data on the neighborhood agree with the reset construction"
  claim (:358-360) becomes an m-point statement; (iii) the μ₁/μ₂ first-return effect
  must be recomputed by cut-splice with m cut tails per color, not 1 (ledger row :36).

Grade **PLAUSIBLE-NEEDS-PROOF** — no W2-style obstruction found: the closure direction
moves no pinned/separating coordinate, which is exactly why this row, unlike X₁/X₂ and
C_h, is compatible with the exact criterion.

### 2.3 Claim 1c — switching_ribbons.tex as a whole (load-bearing for H2-H4, H5)

Per-lemma audit of all 207 lines:

* `def:comparison-switch` :10-19, `lem:partial-exchange` :21-41,
  `lem:layer-comparison-switch` :43-53 — **criterion-exact** (§2.1.i).
* `lem:ribbon-realization` :55-68 — bookkeeping correspondence; proof is terse
  ("preserves and reflects alternating components") but the only content RF2 consumes
  (per-layer union of comparison cycles) is definitional.  Acceptable.
* `lem:cut-splice` :87-107, `lem:return-switch` :109-148,
  `cor:interlacing-selector` :150-174 — return-level permutation algebra; checked the
  identities (H = G∘σ⁻¹ on C etc.); correct, no RF2 content.
* `lem:switching-ribbons` (ribbon composition) :190-207 — **the gap**.  The proof
  asserts "Support disjointness makes the layer exchanges commute on sources and
  images; the source and image sets affected in each layer are disjoint" (:199-200).
  Under the exact criterion this is true only when the ribbons touch pairwise
  DISJOINT COLOR PAIRS: if two ribbons share an affected color c, c's layer map
  becomes three-valued and the single-swap invariances no longer compose — the extra
  obligation `(U₁ + v_{σ₁c}) ∩ (U₂ + v_{σ₂c}) = ∅` is nowhere stated or discharged.
  This is precisely the failure mode measured in
  `H2_REALIZATION_BLOCKER_20260605.md` §8: the D5(4) first-lift and final-lift
  substitutions applied in the same layers force color 0's images onto one fiber
  (image 240 or 204/256, ALL base rows) — an instance of the missing cross-ribbon
  condition, fixed only by layer-indexed separation.
  - For the sans-C_h ENDPOINT family the lemma is safe: X₀ affects {t₀,d₁}, X₁
    {t₁,d₂}, X₂ {t₂,d₃}, R {μ₁,μ₂} — pairwise color-disjoint, so each color's layer
    map stays two-valued and the per-ribbon (★) suffices.  (With C_h present it was
    maximally violated: C_h moves every color, so it shared colors with every ribbon.)
  - For the D5(4) §11 story (D54_parity_reset.tex:191-198 "Insert the five local
    substitutions … rows remain Latin and the layer maps remain bijective … Lemma
    lem:switching-ribbons realizes exactly the five return maps") the composition
    claim is **SUSPECT-LIKE-W2**: the naive reading is empirically RF2-false, and the
    sentence's "realizes exactly the five return maps" additionally needs the wild
    correspondence (blocker §2).
  - H5/doubling consumers should re-check that their ribbon families are color-disjoint
    per layer, or supply the cross-ribbon image conditions explicitly.

Grade: **PLAUSIBLE-NEEDS-PROOF** (general statement), with the explicit caveat above;
the revision should add the color-disjointness (or per-layer cross-image) hypothesis.

### 2.4 Claim 2 — the carry mechanism with the C_h-fiber route excluded

**Ledger and lem:endpoint-completion.**  The return ledger
(endpoint_successor.tex:25-40) row "completion branch θ_ν … one-point carry ±1" and
`lem:endpoint-completion` (:125-178) are abstract skew-product statements: a quotient
one-point carry γ = ±1 at site c_ν plus `lem:unit-carry` gives cyclicity.  This level
is **VERIFIED** and formalized (`EndpointCompletion`, `CompletionTower.towerMap_singleCycle`;
`QUESTION_W2` §3, `E6_DESIGN` §5.3).  The wrong part was only the claim that a
localized `C_h` ROW realizes the crossing (`def:lifted-completion-fiber` :265-281's
"Thus lem:endpoint-completion sees a one-point carry, while
lem:completion-fiber-bijectivity checks RF2 on the full fiber" :278-281).  Note the
ledger row :35 itself names "cyclic completion row C_{h_ν} on a full lifted fiber" —
the ledger TEXT (not its arithmetic) needs revision.

**The swap-based replacement.**  Mechanism: at one layer, swap the appending color's
lane read with the zero-displacement read (or a τ₀-class read) on a cylinder pinning
the quotient site (q, y at the site, z-prefix) and FREE in the swept/hidden
coordinates.  By the §0 key fact these cylinders are (★)-invariant precisely because
both swap directions avoid the pinned block — `E6_DESIGN` §1.2 establishes the
systematic family (α ∈ {τ₀-read, Fin.last-read}); QUESTION_W2 Q3 records the
formalization-side confirmation that RF2-legal one-point carries exist this way.
Each such swap is budget-neutral (mass ≤ 1) — Wall 1 does not bite the carry itself.
Two genuine open obligations:

1. **Wall 3 (donor bookkeeping)**: the swap necessarily perturbs the donor color (the
   one that owned the zero/τ₀ read) — its return gains a lane step at the same sites.
   The revised ledger must track carries in donor/donee pairs; parity counting
   (`E6_DESIGN` §4.3: each line-cut is odd, donations 2·(b−1)·2 even ⇒ paired dummy
   corrections needed) is unresolved and is the real design problem.
2. **Once-per-period firing**: the cylinder's pins must meet each first-return
   trajectory exactly once per period at the quotient site — this is the part of
   `def:lifted-completion-fiber`'s intent that survives and must be re-proved for the
   swap supports.

**Comparison with the ACTUAL D5(4) certificate.**  Facts established by inspection:

* The paper's five substitutions (D54_parity_reset.tex:58-69 T_i/P₀/P₁ on Q₄×Y;
  :110-128 final sites a_i and lifts R̂_i) are verified ONLY at the abstract return
  level: R̂₀..R̂₄ are 256-cycles
  (`CERTIFICATE_VERIFICATION_20260607.md` fact C; `LowD5M4Seed.fullReturn`).
* The shipped certificate `EvenV11/LowD5M4Finite.lean` is a SEARCH-FOUND
  5120-entry `dirTable` (:36) + `dir` (:1724) proving RF1/RF2/RF3 directly by
  `native_decide` (54 occurrences; `schedule_returnsSingleCycle` :1973 via
  `RankArrayCert`).  It is byte-identical to `archive/EvenV11/LowD5M4Finite.lean`,
  for which `H2_PAPER_REALIZATION_COMPUTED_AUDIT_20260607.md` item 5 records: **no
  common conjugacy to `LowD5M4Seed.fullReturn`** — the certificate's returns are NOT
  the paper's R̂_i under any single reindexing, and no decomposition into
  "product word + five substitutions" is exhibited anywhere.
* The paper-faithful naive realization is refuted twice over: displacement
  (`H2_REALIZATION_BLOCKER_20260605.md` §1: returnMap displacement sup 4,4,4 vs
  paperReturn 5,6,6 — the T_i one-point-carry-on-top-of-full-word model is over the
  m-step budget at the crossing) and RF2 (§8: same-layer first+final substitutions
  fail layer bijectivity for every base row).  The identified fix direction —
  layer-indexed (t-dependent) placement of the Y-carry and Z-carry substitutions —
  is exactly the swap-based mechanism above, but it was never built; the search blob
  closed H2 instead.
* No `docs/even_v11_certificate_triage/` directory exists; the relevant triage
  documents are the three cited above plus `CURRENT_STATE_GROUND_TRUTH_20260608.md`
  (H2/H3/H4 closed as finite witnesses).

Precise answer to the audit question: **the ledger's ±1-per-completion arithmetic is
attributable to a swap-based mechanism in principle (RF2-legal, budget-fine,
abstract tower closed), but no actual certificate exhibits it** — where the
certificates are inspectable (D5(4)), the carries are not localizable to the paper's
sites under any coordinate-respecting reading, and the only positive structural
evidence for the donor pattern is the abstract shape of P₀/P₁
(D54_parity_reset.tex:63-69: fiber-indexed terminal words = donor color gaining
terminal reads).  Grade 2b **PLAUSIBLE-NEEDS-PROOF**.

### 2.5 Claim 3 — port-room separation with C_h gone

The support table (general_endpoint_port_room.tex:37-45) and
`lem:endpoint-port-room` (:75-120) carried four separation duties.  Status per duty:

1. **Obsolete (C_h only)**: disjointness of the completion FIBERS from everything —
   `def:lifted-completion-fiber`:273-276 ("The separated row list chooses the sites
   c_ν so that these fibers are disjoint from the terminal-exchange and reset
   cylinders and from the other completion fibers") and the c_j rows of the tables
   (:42, :135) in their fiber reading.  Gone with the route.  The SITES c_ν over
   U_j^c remain useful as quotient sites for the replacement carries (E6 §5.3
   consumes them), but their separation needs are different (see 4 below).
2. **Survives verbatim**: the reset analysis.  The reset closure direction moves only
   z-lanes; parent (c_∗) and terminal (q_R) projections are constant along the line,
   so separation from exchanges/carries by terminal state or parent point is stable
   under closure.  Needed additions are the m-point line statements of §2.2.
3. **Must migrate**: the exchange separations.  Two reasons.  (a) The corrected X_i
   support is the terminal cylinder {q = q_i} × Y × Z, whose parent projection is ALL
   of Y — so "different parent projections give disjoint subsets" (:84) and the
   marked-transfer's "parent supports contained in the complement of N(C)" (:353-355)
   cannot do the work; separation must instead come from the TERMINAL coordinate:
   distinct q₀, q₁, q₂, q_R, and a lifted-cycle terminal state q_C ∉ {q_i, q_R}
   (consistent with :344-345 "the lifted cycle is C with fixed terminal and successor
   coordinates").  This is a clean, checkable replacement story.  (b) Even where
   parent projections are kept (e.g. for seed sites), the X_i closure direction moves
   the parent lane y_i, so any parent-projection-based claim must hold for the
   e_{y_i}-line closure of U_i — an admissibility condition on
   `def:marked-rootflat-datum` that is currently absent.
4. **New duties for the replacement mechanism**: the swap-based carry cylinders pin
   (q, y-site, z-prefix) and are free in (z-suffix, slack); pairwise disjointness and
   disjointness from {q = q_i}, the reset line, and the N(C) lift are determined by
   the pinned coordinates — a finite system of "distinct pins" conditions exactly in
   the spirit of the existing proof (:98-103), plus the new endpoint reserve cylinder
   (:104-119), which survives unchanged (its separation is by the parent point u_∗,
   which no surviving closure direction moves… EXCEPT the X_i closures; so the
   reserve too should add a terminal-state pin q_∗ ∉ {q_i}, which :104-113 already
   provides — "independently of the terminal state q_∗" must become "with q_∗ chosen
   distinct").

Grade **PLAUSIBLE-NEEDS-PROOF**: a consistent disjointness story exists, but it is a
different story (terminal-state pins, line-closed supports) than the printed
parent-projection story.

### 2.6 Claim 4 — high-even spot checks (grade only, one paragraph each)

**(a) `lem:quotient-to-layer-support-lift` (high_even_seed_realization.tex:363-392):
PLAUSIBLE-NEEDS-PROOF.**  Unlike C_h, this lemma works directly at the image level —
injectivity on S via the bijection of old heads onto a rank-one quotient line T with
fixed fiber coordinates (:384-388), plus image-disjointness from the complement.  The
two-valued criterion is exactly "injective on each branch + cross-branch image
disjointness", so the MECHANISM is criterion-compatible.  The gap is that the
disjointness is discharged by the phrase "whenever the prescribed support sets are
separated" (:377) / "the support-separation hypotheses put this head line outside the
image of every source in the complement" (:388-390): source-support separation does
NOT imply head-line-vs-old-image separation (this is precisely the W2 conflation —
`lem:completion-fiber-bijectivity`:295-297 used the same phrase), and the consumers
(`lem:seed-forest-realization` :394-408, `lem:seed-laminar-composition` :410-425)
discharge it with laminar SOURCE intervals only.  Not suspect — the new heads here are
single-coordinate increments on a controlled line, and laminar nesting plausibly
implies the image condition — but the hypothesis must be restated at image level and
re-checked per consumer.

**(b) `lem:one-step-packet-splice` (:467-494): VERIFIED at its own level.**  It is a
pure return-permutation statement (cut tails a_j, reconnect a_j → h_{j+1}, concatenate
q coset-cycles into one), proved by interval concatenation; no layer/RF2 content, no
two-valued model, so the W2 issue cannot infect it directly.  Its REALIZATION as layer
rows (the new edge a_j → h_{j+1} displaces by a non-unit vector in v + H) is delegated
to (a) and inherits (a)'s sharpened-hypothesis obligation; flagged, not graded down.

## 3. Revision guidance (what the paper must state, per surviving mechanism)

1. **X₀ exchange**: restate the support as the terminal cylinder
   U_{X₀} = {q = q₀} × Y × Z (or, if singleton seeds are kept, define S_{X₀} so its
   ribbon closure is this cylinder), note the (★)-check
   (e_{p₁⁺} − e_{τ₀} avoids the pinned q-block), and keep the exponent-1 ledger.
   State explicitly that "the inserted parent step realizes P₀" is a template-level
   identification (run-collapse), not a layer-level identity.
2. **X₁, X₂**: cannot stand as printed.  Options the revision must choose among:
   (i) replace the firing condition so the pinned block avoids τ₁/τ₂ (e.g. fire on a
   z/y-pinned cylinder and re-derive the exponent calculation — changes
   `lem:endpoint-active-core`); (ii) route both exchanges through τ₀-class reads with
   an explicit multi-layer donor bookkeeping (the Wall-3 calculus, currently
   nonexistent); (iii) drop the per-layer locality claim and state the wild
   correspondence as an assumption.  Whichever is chosen, the erratum should record
   the b = 4 counterexample (decide-able) alongside the W2 one.
3. **Reset R**: redefine the localized support as the m-point comparison line
   r₀ + ⟨ε₂⁻ − ε₁⁻⟩ (containing both tails); keep `lem:endpoint-reset-common-image`
   but add the post-switch version (μ₂(r₀) = μ₁(r₁) = I) and say which configuration
   carries the marked edge; recompute the μ₁/μ₂ cut-splice with m tails; restate the
   marked-transfer interaction with N(C) as an m-point condition over c_∗.
4. **Completion carries**: replace `def:lifted-completion-fiber` +
   `lem:completion-fiber-bijectivity` + the C_h row of
   `lem:endpoint-local-row-realization` by per-coordinate two-color swap rows
   ((appending lane, zero/τ₀-class read) pairs) on pinned-cylinder supports from the
   legal family, with: the (★)-check per swap, the once-per-period firing lemma, and
   the donor-pair ledger (the donor color's return correction and its parity
   accounting).  Update ledger row :35 and the trace example :180-192 accordingly.
   `lem:endpoint-completion` itself survives once "the chosen cyclic row C_{h_ν}"
   (:135-137) is replaced by the swap-site crossing.
5. **Port room**: rewrite the support table with terminal-state pins as the primary
   separator for exchanges (distinct q₀,q₁,q₂,q_R,q_C,q_∗), keep parent-point
   separation only for line-closed supports, and add the closure-admissibility
   condition on the parent supports U_i (closed under the relevant lane lines) to
   `def:marked-rootflat-datum`.
6. **switching_ribbons.tex**: add the color-disjointness hypothesis (or the explicit
   cross-ribbon image condition) to `lem:switching-ribbons`, and note that the
   endpoint family satisfies it while multi-substitution applications (D5(4) §11)
   must verify per-layer placement — with a pointer to the layer-indexed fix.
7. **D5(4) §11**: the realization paragraph (:191-205) should either present a
   layer-indexed substitution schedule that passes RF2, or honestly state that the
   construction is certified by a finite witness whose row structure is not the five
   substitutions.

## 4. Formalization guidance (wild-e / E-phase design targets, sans C_h)

Surviving mechanisms and their Lean obligations:

1. **Keep as the RF2 backbone**: `EndpointRowSchedule.LayerDesc` +
   `rowSchedule_layerBijective_of_plan`, extended by the two E6c-pre items
   (`E6_DESIGN` §7): block-product RF2 (state-dependent Q-block ⊗ lane permutation)
   and the w₀-free cylinder lemma (Φ as AddEquiv + period dictionary).  These cover
   every layer shape the revised design needs: constant rows, X₀-type swaps,
   reset-type swaps, carry swaps.
2. **X₀-type layers**: instantiate `exchangeDesc` with U = the q-pinned cylinder; the
   invariance proof is the §0 key fact (mechanical).  Do NOT build X₁/X₂ descriptors
   on q-pinned cylinders — record instead the negative theorem (b = 4, m = 4 decide;
   parametric by the one-coordinate version of the W2 lattice argument) in
   `EndpointNegative.lean` next to `EndpointChRowObstruction` (E6d slot).
3. **Reset layers**: instantiate `resetDesc` with U = the d-line through r₀
   (`EndpointPortRoom.ResetPair` already proves `common_image_eq`; add the line-closure
   set and its invariance — one-line proof, U is a union of d-cosets).
4. **Carry layers (the E-phase core)**: one descriptor per appended coordinate:
   swap (lane read, zero/τ₀-class read) on a cylinder pinning the level-ν quotient
   site, free in z-suffix and slack.  Obligations: (a) (★) per swap — free, by the
   key cylinder fact; (b) once-per-period crossing — a new lemma tying the cylinder
   pins to the first-return trajectory (this replaces
   `def:lifted-completion-fiber`'s surviving intent); (c) the DONOR correction: the
   zero-owner color's return gains lane steps at the same sites — this must be
   threaded into the seed models of `EndpointSeedReturns` (the §5.4 muSeed/P₀-shape
   pattern is the right template) with the parity pairing of Wall 3 resolved by
   explicit dummy swap pairs.  This is the genuinely new mathematics; budget it as a
   design note BEFORE Lean.
5. **Return identification**: all of the above produces single carries and swaps at
   the row level; the identification with the ledger models (P_i insertion, exponent
   m²−1) remains the per-color wild run-collapse `e_c` of
   `EndpointRunCollapseRealization` (`EndpointRealization.lean`, Main :447).  The
   re-audit does not change that interface's shape; it confirms that (i) the seed
   models (E6b) and the carry tower stay as the conjugation targets, (ii) the row
   side should be assembled from exactly the descriptor shapes in 1-4, so that the
   wild-e design problem is isolated in `conj` and nothing else.  H1b's common-e and
   this per-color e_c remain one design effort (`E6_DESIGN` §6).
6. **Composition hygiene**: when assembling the full plan, keep ribbon/swap families
   color-disjoint PER LAYER (the sans-C_h endpoint family is; carry swaps must be
   scheduled into layers so no color sees two substitutions in one layer — the
   t-indexed dir fix of blocker §8 elevated to a design rule).  A small Lean lemma
   "color-disjoint swap families compose" (multi-cylinder `LayerDesc` variant) would
   make `lem:switching-ribbons`'s safe case criterion-exact and reusable for H5.

## 5. Source inventory used

* Paper: endpoint_successor.tex (377 l), switching_ribbons.tex (207 l),
  general_endpoint_port_room.tex (139 l), endpoint_b4_chart.tex (69 l),
  D54_parity_reset.tex (205 l), high_even_seed_realization.tex (:200-500).
* Lean: `EvenV11/V28Hard/EndpointRowSchedule.lean`, `EndpointChart.lean`,
  `EndpointPortRoom.lean` (ResetPair :67-152), `EvenV11/LowD5M4Finite.lean`
  (dirTable :36, dir :1724, RF3 :1973; byte-identical to archive blob).
* Docs: `QUESTION_W2_COMPLETION_FIBER_20260610.md`, `E6_DESIGN_20260610.md`,
  `H2_REALIZATION_BLOCKER_20260605.md` (§1, §4, §4.1, §8),
  `H2_PAPER_REALIZATION_COMPUTED_AUDIT_20260607.md`,
  `CERTIFICATE_VERIFICATION_20260607.md`, `H1B_REALIZATION_OBSTRUCTION_20260609.md`,
  `CURRENT_STATE_GROUND_TRUTH_20260608.md`,
  `FORMALIZATION_STATUS_AND_PLAN_20260609.md`.
  (No `docs/even_v11_certificate_triage/` directory exists; the certificate-triage
  content lives in the three H2/certificate docs above.)
