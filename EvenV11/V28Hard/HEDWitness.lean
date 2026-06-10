import EvenV11.RootFlatCycleData
import EvenV11.GuideLocality

/-!
# `HEDWitness` — the certificate-grows witness for the high-even growth engine

G2 of the growth-engine plan (`docs/GROWTH_ENGINE_DESIGN_20260610.md` §3 G2).
This is the Lean form of the paper's high-even chain datum `HED(D, m)`
(rewritten manuscript `/data/angel/repos/etc/even_modulus_rewrite_20260610/`,
`subtex/high_even_chain_datum.tex`, `def:high-even-chain-datum`) over the
marked root-flat datum with endpoint reserve
(`subtex/induction_data_reserved_sites.tex`, `def:marked-rootflat-datum`,
`def:endpoint-ready-reserve`, `lem:admissible-singleton-reserve`).

Why a `Type`-valued witness and not the bare target: design-doc Part 1.3 —
the naive block-diagonal growth ("old `dir` literally unchanged, new colors
read their own leaf") FAILS RF3 for the new colors, so each growth step
re-realizes the schedule over the relabeled `D + 2` chart and continues the
old system at the quotient level.  The bare `FinalMarkedTarget d m`
(`Shared.TorusHamiltonDecomposition`, a `Prop`) carries none of the interface
the next step consumes (`EndpointParentCycle` showed only the abstract parent
cycle is extractable), so the induction must carry a full witness and project
the bare target only at the very end.

Conventions (torus dimension `d = n + 1`, exactly as `RootFlatCycleData`):

* `cycleData` — the realized layer schedule at the current dimension:
  a concrete `dir` over the standard lift plus RF1/RF2/RF3.
* `selector` — the marked layer (paper `def:marked-rootflat-datum` item 1, in
  the singleton common-edge form of the dimension-7 gate report; clause
  semantics mirrored from the rewrite's
  `certificates/scripts/check_hed_clauses.py`): two marked colors, a selector
  point `c`, the common image `I`, the protected neighborhood `N(C)`, with the
  closure (`R_a(c) = R_b(c) = I`), unit (`|C| = 1` a unit mod `m`) and
  post-switch-cyclicity clauses as `Prop` fields.
* `reserve` — the endpoint reserve: `(n + 1) + 3` reserve singletons in the
  one fixed-fiber form (chain item 6 / the script's
  "fixed-fiber form: all reserve states in one (Q,Z)-fiber" clause): all
  sites agree outside the listed free coordinates, are pairwise distinct, and
  are separated from `N(C)` *in the fixed coordinates*.
* `chain` — chain items 2–5 in the OUTPUT chart `ZMod (n + 3)` of the next
  growth step: the label chart (two new labels + old-label embedding), the
  row-indexed growth interface (ordered support, leaf line, quotient
  direction, translated old generators `𝒢⁻_r`, phase `ρ`), and the separated
  terminal `A₂` carrier.  The midpoint translate rule (item 4) is a formula,
  not data — exposed as `ChainFields.guideCenters` via
  `GuideLocality.AdditiveTripleGuideList`.

Deliberate prunings against the design-doc sketch (its own minimality rule:
"a field enters only if G4 consumes it"):

* no `hD/hodd/hm/hev` range fields — the dimension shape is carried by the
  `∀ k, 3 ≤ k → GrowthStep (2 * k) m` quantifier of the driver and the
  modulus hypotheses are hypotheses of G4's step *constructions*
  (design doc 1.4: `m` enters only through `IsUnit (±1)`, leaf-fiber room and
  `NeZero` — conditions for building a step, not for applying one);
* no `oldGensSpec`/`quotient` certificate fields yet — the inactive-flag span
  condition `H⁻_r = ⟨𝒢⁻_r, L_{r'} : r' < r⟩` (`lem:chain-old-span`) and the
  per-color quotient normal forms are the semantic glue whose exact Lean form
  G4 determines; the witness carries the generator *data* those conditions
  are about.

Every `Prop` field is decidable-friendly at fixed `(n, m)` (G3 fills them by
`native_decide` at `(7,4)/(7,6)`), except the two clauses that are
decidable-by-construction instead: the unit clause (filled by `isUnit_one`)
and the post-switch clauses (filled from RF3 — the Lean form of the paper's
`lem:singleton-common-edge-selector`: a singleton common edge makes the
switch the identity, so post-switch cyclicity *is* RF3).  Bool-valued audits
with `_holds` bridges (the `FiniteAudit` house pattern) are provided for the
clause groups.

No `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace EvenV11
namespace V28Hard
namespace HEDWitness

open Shared StandardRootFlatLift RootFlatCycle

/-! ## The marked layer: singleton common-edge selector

Paper `def:marked-rootflat-datum` item 1 in the singleton witness form of the
dimension-7 certificates (`check_hed_clauses.py`: marked colors / selector
`c` / common image `I` / `|C| = 1` unit / post-switch cyclicity / protected
neighborhood).  The dimension-7 `m ∈ {4, 6}` instances of exactly this data
ship as `FoldedCommonEdgeWitness.SingletonCommonEdgeWitness`; that structure
is folded-coordinate-specific (`FoldedCoord m`, six coordinates), so the
parametric form here works directly with `RootState n m` points relative to a
given schedule `dir`. -/

/-- Singleton common-edge selector for the schedule `dir`: marked colors
`a ≠ b`, a selector point `c` and the common image `I` with
`R_a(c) = R_b(c) = I` (the closure clause; since `returnMap` is the fold of
the `m` layer maps this is simultaneously the layer-level path clause checked
by the gate report), the unit clause `|C| = 1` in `ZMod m`, the post-switch
cyclicity clause, and the protected neighborhood `N(C)` containing `c` and
`I`. -/
structure MarkedSelector (n m : Nat) [NeZero m]
    (dir : ZMod m → RootState n m →
      Shared.TorusColor (n + 1) → Shared.TorusDirection (n + 1)) : Type where
  /-- first marked color `a`. -/
  firstColor : Shared.TorusColor (n + 1)
  /-- second marked color `b`. -/
  secondColor : Shared.TorusColor (n + 1)
  /-- the selector point `c` (the singleton comparison cycle `C = {c}`). -/
  point : RootState n m
  /-- the common image `I = R_a(c) = R_b(c)`. -/
  commonImage : RootState n m
  /-- the protected neighborhood `N(C)` (selector, image, and the
  predecessor/successor data of `C` in the marked returns). -/
  protectedPoints : List (RootState n m)
  /-- the two marked colors are distinct. -/
  colors_ne : firstColor ≠ secondColor
  /-- closure clause for `a`: the first marked return sends `c` to `I`. -/
  closure_first : (schedule dir).returnMap firstColor point = commonImage
  /-- closure clause for `b`: the second marked return sends `c` to `I`. -/
  closure_second : (schedule dir).returnMap secondColor point = commonImage
  /-- unit clause: `|C| = 1` is a unit modulo `m`
  (`def:marked-rootflat-datum` item 1; always fillable by `isUnit_one`). -/
  card_unit : IsUnit ((1 : ZMod m))
  /-- post-switch cyclicity for `a`: switching on the singleton `C` is the
  identity, so the post-switch return is the return itself — fill from RF3
  (`lem:singleton-common-edge-selector`). -/
  postSwitch_first : Shared.IsSingleCycleMap ((schedule dir).returnMap firstColor)
  /-- post-switch cyclicity for `b`. -/
  postSwitch_second : Shared.IsSingleCycleMap ((schedule dir).returnMap secondColor)
  /-- `c ∈ N(C)`. -/
  point_mem_protected : point ∈ protectedPoints
  /-- `I ∈ N(C)`. -/
  image_mem_protected : commonImage ∈ protectedPoints
  /-- the protected points are pairwise distinct. -/
  protected_nodup : protectedPoints.Nodup

/-- Bool audit of the decidable selector clauses (everything except the unit
and post-switch clauses, which are decidable-by-construction).  G3 closes this
by `native_decide` at fixed `(n, m)`. -/
def selectorClausesBool {n m : Nat} [NeZero m]
    (dir : ZMod m → RootState n m →
      Shared.TorusColor (n + 1) → Shared.TorusDirection (n + 1))
    (a b : Shared.TorusColor (n + 1)) (point commonImage : RootState n m)
    (protectedPoints : List (RootState n m)) : Bool :=
  decide (a ≠ b) &&
    decide ((schedule dir).returnMap a point = commonImage) &&
    decide ((schedule dir).returnMap b point = commonImage) &&
    decide (point ∈ protectedPoints) &&
    decide (commonImage ∈ protectedPoints) &&
    decide protectedPoints.Nodup

/-- `_holds` bridge for `selectorClausesBool` (FiniteAudit house pattern). -/
theorem selectorClausesBool_holds {n m : Nat} [NeZero m]
    {dir : ZMod m → RootState n m →
      Shared.TorusColor (n + 1) → Shared.TorusDirection (n + 1)}
    {a b : Shared.TorusColor (n + 1)} {point commonImage : RootState n m}
    {protectedPoints : List (RootState n m)}
    (h : selectorClausesBool dir a b point commonImage protectedPoints = true) :
    a ≠ b ∧
      (schedule dir).returnMap a point = commonImage ∧
      (schedule dir).returnMap b point = commonImage ∧
      point ∈ protectedPoints ∧
      commonImage ∈ protectedPoints ∧
      protectedPoints.Nodup := by
  simp only [selectorClausesBool, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Build a `MarkedSelector` over a full cycle-data from the single Bool
audit: the unit clause is `isUnit_one` and the post-switch clauses are RF3
(`lem:singleton-common-edge-selector`). -/
def MarkedSelector.ofBool {n m : Nat} [NeZero m]
    (data : RootFlatCycleData n m)
    (a b : Shared.TorusColor (n + 1)) (point commonImage : RootState n m)
    (protectedPoints : List (RootState n m))
    (h : selectorClausesBool data.dir a b point commonImage protectedPoints
      = true) :
    MarkedSelector n m data.dir :=
  have hc := selectorClausesBool_holds h
  { firstColor := a
    secondColor := b
    point := point
    commonImage := commonImage
    protectedPoints := protectedPoints
    colors_ne := hc.1
    closure_first := hc.2.1
    closure_second := hc.2.2.1
    card_unit := isUnit_one
    postSwitch_first := data.returnsSingleCycle a
    postSwitch_second := data.returnsSingleCycle b
    point_mem_protected := hc.2.2.2.1
    image_mem_protected := hc.2.2.2.2.1
    protected_nodup := hc.2.2.2.2.2 }

/-! ## The endpoint reserve: `(n + 1) + 3` singletons in one fixed fiber

Paper `def:endpoint-ready-reserve` + `lem:admissible-singleton-reserve` in
the fixed-fiber transport form of chain item 6: the ordered family
`(U_0, U_1, U_2, U^c_1, …, U^c_{d-1}, U_*)` (`d + 3 = n + 4` singletons,
order carried by the list) lies in a single fiber of the coordinates outside
`freeCoords` — at the dimension-7 bases this is the printed
`(y; m-1, m-1; 0, 0)` form with `freeCoords` the two `y`-coordinates.  The
folded `ReserveRole`/`ReserveState` tables of `FoldedReserveSeparation` are
the `(7, 4)/(7, 6)` instances of this data; they are dimension-specific
(ten fixed roles, six folded coordinates), hence the parametric list form
here. -/

/-- Endpoint reserve in fixed-fiber form: `n + 4` pairwise distinct sites,
all agreeing outside the free coordinates. -/
structure ReserveSites (n m : Nat) [NeZero m] : Type where
  /-- the ordered reserve singletons
  `U_0, U_1, U_2, U^c_1, …, U^c_{n}, U_*` (order = role order). -/
  sites : List (RootState n m)
  /-- the moving coordinates of the reserve fiber; every other coordinate is
  pinned (the "all new leaf coordinates fixed" clause of chain item 6). -/
  freeCoords : List (Fin n)
  /-- reserve count is `d + 3 = (n + 1) + 3`. -/
  count : sites.length = n + 4
  /-- the reserve singletons are pairwise distinct. -/
  nodup : sites.Nodup
  /-- one fixed-fiber form: any two sites agree on every pinned coordinate. -/
  fixedFiber : ∀ p ∈ sites, ∀ q ∈ sites, ∀ i : Fin n, i ∉ freeCoords → p i = q i

/-- Bool audit of the reserve clauses. -/
def reserveClausesBool {n m : Nat} [NeZero m]
    (sites : List (RootState n m)) (freeCoords : List (Fin n)) : Bool :=
  decide (sites.length = n + 4) &&
    decide sites.Nodup &&
    decide (∀ p ∈ sites, ∀ q ∈ sites, ∀ i : Fin n, i ∉ freeCoords → p i = q i)

/-- `_holds` bridge for `reserveClausesBool`. -/
theorem reserveClausesBool_holds {n m : Nat} [NeZero m]
    {sites : List (RootState n m)} {freeCoords : List (Fin n)}
    (h : reserveClausesBool sites freeCoords = true) :
    sites.length = n + 4 ∧ sites.Nodup ∧
      ∀ p ∈ sites, ∀ q ∈ sites, ∀ i : Fin n, i ∉ freeCoords → p i = q i := by
  simp only [reserveClausesBool, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

/-- Build `ReserveSites` from the single Bool audit. -/
def ReserveSites.ofBool {n m : Nat} [NeZero m]
    (sites : List (RootState n m)) (freeCoords : List (Fin n))
    (h : reserveClausesBool sites freeCoords = true) : ReserveSites n m :=
  have hc := reserveClausesBool_holds h
  { sites := sites
    freeCoords := freeCoords
    count := hc.1
    nodup := hc.2.1
    fixedFiber := hc.2.2 }

/-! ## Chain fields: items 2–5 of `def:high-even-chain-datum`

All labels live in the OUTPUT chart `ZMod (n + 3)` of the next growth step
(`= ZMod (D + 2)`, `D = n + 1`): paired step relabels the new labels to
`{0, 3}`; the special chained `7 → 9` step identifies the dimension-7 labels
with `ZMod 9 \ {0, 1}` (the gate report's label-chart/carrier arithmetic
clauses).  The row shapes mirror `GuideLocality`'s audited growth-row tables
(`ordinaryHighEvenRowSupport/LeafLine/QuotientGenerator/Delta`, phases
`ρ = 3, 7` ordinary and `1, 5` chained). -/

/-- Row-indexed growth interface (chain item 3) for one growth row, in the
output chart: ordered local support `A_r`, leaf line `L_r`, quotient
direction `g_r`, the translated old incidence generators `𝒢⁻_r`, plus the
phase `ρ` and step `δ_r` feeding the midpoint translate rule (item 4).  The
inactive-flag span condition `H⁻_r = ⟨𝒢⁻_r, L_{r'} : r' < r⟩`
(`lem:chain-old-span`) is the property of the realization that G4
establishes; the witness carries the generator data it is about. -/
structure GrowthRowInterface (n : Nat) : Type where
  /-- ordered local support `A_r` (chart labels). -/
  support : List (ZMod (n + 3))
  /-- leaf line `L_r` (endpoint pair, as in
  `GuideLocality.ordinaryHighEvenRowLeafLine`). -/
  leafLine : ZMod (n + 3) × ZMod (n + 3)
  /-- quotient direction `g_r` (endpoint pair). -/
  quotientGen : ZMod (n + 3) × ZMod (n + 3)
  /-- translated old incidence generators `𝒢⁻_r` (oriented label pairs). -/
  oldGens : List (ZMod (n + 3) × ZMod (n + 3))
  /-- the boundary-avoiding phase `ρ` chosen for this row. -/
  phase : ZMod (n + 3)
  /-- the midpoint step `δ_r` of the translate rule. -/
  delta : ZMod (n + 3)

/-- Chain items 2 (label chart), 3–4 (row-indexed interface), and
5 (separated terminal carrier). -/
structure ChainFields (n : Nat) : Type where
  /-- the two new labels of the output chart (`(0, 3)` paired,
  `(0, 1)` chained). -/
  newLabels : ZMod (n + 3) × ZMod (n + 3)
  /-- embedding of the current labels into the output chart
  (the old-label summand `W_{D+2} \ newLabels`). -/
  oldLabel : Fin (n + 1) → ZMod (n + 3)
  /-- the two growth rows the next step may use. -/
  rows : Fin 2 → GrowthRowInterface n
  /-- the three-label terminal `A₂` carrier (`{3, 4, 6}` in the chained
  chart). -/
  carrier : Fin 3 → ZMod (n + 3)
  /-- the two new labels are distinct. -/
  newLabels_ne : newLabels.1 ≠ newLabels.2
  /-- the old-label embedding is injective (with the next two clauses it is a
  bijection onto the old-label summand, by cardinality). -/
  oldLabel_inj : Function.Injective oldLabel
  /-- old labels avoid the two new labels. -/
  oldLabel_avoids_new : ∀ i, oldLabel i ≠ newLabels.1 ∧ oldLabel i ≠ newLabels.2
  /-- the three carrier labels are distinct. -/
  carrier_inj : Function.Injective carrier
  /-- the carrier lies on the old-label summand. -/
  carrier_on_old : ∀ j, ∃ i, carrier j = oldLabel i
  /-- carrier separation (item 5): the carrier summand is disjoint from every
  label used by the growth window. -/
  carrier_avoids_supports : ∀ j, ∀ r, carrier j ∉ (rows r).support

/-- Midpoint translate rule (chain item 4): row `r` tests translated old
lines only through the three midpoint centers
`G_{r,ρ} = {ρ - δ_r, ρ, ρ + δ_r}`.  This is a formula, not free data —
exactly `GuideLocality.AdditiveTripleGuideList`. -/
def ChainFields.guideCenters {n : Nat} (cf : ChainFields n) (r : Fin 2) :
    List (ZMod (n + 3)) :=
  GuideLocality.AdditiveTripleGuideList ((cf.rows r).phase) ((cf.rows r).delta)

/-- Bool audit of the chain clauses. -/
def chainClausesBool {n : Nat}
    (newLabels : ZMod (n + 3) × ZMod (n + 3))
    (oldLabel : Fin (n + 1) → ZMod (n + 3))
    (rows : Fin 2 → GrowthRowInterface n)
    (carrier : Fin 3 → ZMod (n + 3)) : Bool :=
  decide (newLabels.1 ≠ newLabels.2) &&
    decide (Function.Injective oldLabel) &&
    decide (∀ i, oldLabel i ≠ newLabels.1 ∧ oldLabel i ≠ newLabels.2) &&
    decide (Function.Injective carrier) &&
    decide (∀ j, ∃ i, carrier j = oldLabel i) &&
    decide (∀ j, ∀ r, carrier j ∉ (rows r).support)

/-- `_holds` bridge for `chainClausesBool`. -/
theorem chainClausesBool_holds {n : Nat}
    {newLabels : ZMod (n + 3) × ZMod (n + 3)}
    {oldLabel : Fin (n + 1) → ZMod (n + 3)}
    {rows : Fin 2 → GrowthRowInterface n}
    {carrier : Fin 3 → ZMod (n + 3)}
    (h : chainClausesBool newLabels oldLabel rows carrier = true) :
    newLabels.1 ≠ newLabels.2 ∧
      Function.Injective oldLabel ∧
      (∀ i, oldLabel i ≠ newLabels.1 ∧ oldLabel i ≠ newLabels.2) ∧
      Function.Injective carrier ∧
      (∀ j, ∃ i, carrier j = oldLabel i) ∧
      ∀ j, ∀ r, carrier j ∉ (rows r).support := by
  simp only [chainClausesBool, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Build `ChainFields` from the single Bool audit. -/
def ChainFields.ofBool {n : Nat}
    (newLabels : ZMod (n + 3) × ZMod (n + 3))
    (oldLabel : Fin (n + 1) → ZMod (n + 3))
    (rows : Fin 2 → GrowthRowInterface n)
    (carrier : Fin 3 → ZMod (n + 3))
    (h : chainClausesBool newLabels oldLabel rows carrier = true) :
    ChainFields n :=
  have hc := chainClausesBool_holds h
  { newLabels := newLabels
    oldLabel := oldLabel
    rows := rows
    carrier := carrier
    newLabels_ne := hc.1
    oldLabel_inj := hc.2.1
    oldLabel_avoids_new := hc.2.2.1
    carrier_inj := hc.2.2.2.1
    carrier_on_old := hc.2.2.2.2.1
    carrier_avoids_supports := hc.2.2.2.2.2 }

/-! ## The witness -/

/-- The Lean `HED(D, m)` for torus dimension `D = n + 1`: the certificate-level
chain-data-carrying witness propagated by the growth engine
(`def:high-even-chain-datum`).  A `Type`, not a `Prop`: growth steps consume
the concrete fields. -/
structure HEDWitness (n m : Nat) [NeZero m] : Type where
  /-- realized layer schedule at the current dimension:
  `dir` + RF1 + RF2 + RF3 (chain item 1, root-flat part). -/
  cycleData : RootFlatCycleData n m
  /-- the marked layer over this very schedule (chain item 1, marked part). -/
  selector : MarkedSelector n m cycleData.dir
  /-- the endpoint reserve in fixed-fiber form (chain items 1 and 6). -/
  reserve : ReserveSites n m
  /-- root-flat traces of the switching ribbons already used to build the
  schedule (the set `S` of `lem:admissible-singleton-reserve`; the seven-site
  ledger at the dimension-7 bases). -/
  usedTraces : List (RootState n m)
  /-- chain items 2–5, in the output chart of the next growth step. -/
  chain : ChainFields n
  /-- reserve separation from the protected neighborhood, witnessed in the
  pinned coordinates (the gate report's "terminal projection absent from all
  protected points" clause; implies plain disjointness from `N(C)`). -/
  reserveSeparated : ∀ p ∈ selector.protectedPoints, ∀ q ∈ reserve.sites,
    ∃ i : Fin n, i ∉ reserve.freeCoords ∧ p i ≠ q i
  /-- the reserve singletons avoid all used switching traces
  (`lem:admissible-singleton-reserve`'s exclusion of `S`). -/
  reserveAvoidsTraces : ∀ q ∈ reserve.sites, q ∉ usedTraces

/-- Bool audit of the two witness-level separation clauses. -/
def reserveSeparationBool {n m : Nat} [NeZero m]
    (protectedPoints sites : List (RootState n m))
    (freeCoords : List (Fin n)) (usedTraces : List (RootState n m)) : Bool :=
  decide (∀ p ∈ protectedPoints, ∀ q ∈ sites,
      ∃ i : Fin n, i ∉ freeCoords ∧ p i ≠ q i) &&
    decide (∀ q ∈ sites, q ∉ usedTraces)

/-- `_holds` bridge for `reserveSeparationBool`. -/
theorem reserveSeparationBool_holds {n m : Nat} [NeZero m]
    {protectedPoints sites : List (RootState n m)}
    {freeCoords : List (Fin n)} {usedTraces : List (RootState n m)}
    (h : reserveSeparationBool protectedPoints sites freeCoords usedTraces
      = true) :
    (∀ p ∈ protectedPoints, ∀ q ∈ sites,
      ∃ i : Fin n, i ∉ freeCoords ∧ p i ≠ q i) ∧
      ∀ q ∈ sites, q ∉ usedTraces := by
  simp only [reserveSeparationBool, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-! ## Projections (closed)

The E6c output funnel: `cycleData` →
`finalRootFlatTorusCertificate_of_cycleData` →
`finalRootFlatMarkedTarget_of_certificate`, plus the real-content refinement
of the (previously `PUnit`-fillable) `FinalMarkedEvidence`. -/

/-- Project the root-flat certificate (`lem:chain-datum-forgetful`, first
forgetful step). -/
theorem HEDWitness.toCertificate {n m : Nat} [NeZero m]
    (w : HEDWitness n m) : FinalRootFlatTorusCertificate (n + 1) m :=
  finalRootFlatTorusCertificate_of_cycleData w.cycleData

/-- Project the bare marked target — an actual Hamilton decomposition of
`D_{n+1}(m)` (`lem:chain-datum-forgetful`). -/
theorem HEDWitness.toMarkedTarget {n m : Nat} [NeZero m]
    (w : HEDWitness n m) : FinalMarkedTarget (n + 1) m :=
  finalRootFlatMarkedTarget_of_certificate w.toCertificate

/-- The real-content marked evidence: `HEDWitness` refines the previously
`PUnit`-fillable `FinalMarkedEvidence` with the actual selector and reserve
types. -/
def HEDWitness.toEvidence {n m : Nat} [NeZero m]
    (w : HEDWitness n m) : FinalMarkedEvidence (n + 1) m where
  ComparisonSelector := MarkedSelector n m w.cycleData.dir
  comparisonSelectorWitness := ⟨w.selector⟩
  EndpointReserve := ReserveSites n m
  endpointReserveWitness := ⟨w.reserve⟩

/-- Project the marked payload (target + nonempty evidence). -/
theorem HEDWitness.toMarkedPayload {n m : Nat} [NeZero m]
    (w : HEDWitness n m) : FinalMarkedPayload (n + 1) m where
  target := w.toMarkedTarget
  evidence := ⟨w.toEvidence⟩

/-! ## The growth-step interface and the chain-propagation driver

The step is the shape G4 fills (`prop:paired-growth` /
`prop:chained-two-hole`): one application takes the witness two dimensions
up, re-realizing the schedule over the relabeled chart (design doc 1.3).
Side conditions: the modulus hypotheses (`Even m`, `4 ≤ m`) are hypotheses of
G4's step *constructions* — whoever builds the family
`∀ k, 3 ≤ k → GrowthStep (2 * k) m` has them in scope — and the dimension
bound is carried by the `3 ≤ k` quantifier, so `apply` itself is bare.  No
`m`-vs-`D` comparison appears anywhere (`lem:growth-modulus-free`): the
driver may cross the `D = m` line. -/

/-- One growth step `D → D + 2` at even root dimension `n = D - 1`:
the shape G4's `chainedGrowth` (`n = 6`) and `pairedGrowth` (`n ≥ 8`)
constructions fill. -/
structure GrowthStep (n m : Nat) [NeZero m] : Type where
  /-- apply the step: consume the chain-data witness at root dimension `n`,
  produce the witness at `n + 2`. -/
  apply : HEDWitness n m → HEDWitness (n + 2) m

/-- Iterate growth steps from the dimension-7 base (`n = 6 = 2 * 3`): after
`j` steps the witness lives at root dimension `2 * (j + 3)`.  Pure structural
recursion; the index arithmetic `2 * (j + 1 + 3) = 2 * (j + 3) + 2` is
definitional. -/
def iterateSteps {m : Nat} [NeZero m]
    (step : ∀ k, 3 ≤ k → GrowthStep (2 * k) m)
    (base : HEDWitness 6 m) : (j : Nat) → HEDWitness (2 * (j + 3)) m
  | 0 => base
  | j + 1 => (step (j + 3) (by omega)).apply (iterateSteps step base j)

/-- Witness-level chain closure (the G5 shape, `cor:odd-chain-propagation` at
witness granularity): a base witness at dimension 7 grows to every even root
dimension `2 * k ≥ 6`. -/
def growTo {m : Nat} [NeZero m]
    (step : ∀ k, 3 ≤ k → GrowthStep (2 * k) m)
    (base : HEDWitness 6 m) {k : Nat} (hk : 3 ≤ k) :
    HEDWitness (2 * k) m :=
  (show 2 * (k - 3 + 3) = 2 * k by omega) ▸ iterateSteps step base (k - 3)

/-- The chain-propagation driver (`cor:odd-chain-propagation`, closed modulo
the step): from a dimension-7 witness (`n = 6`), every odd `d ≥ 7` gets the
bare marked target.  Arithmetic: odd `d = 2 * k + 1` with `k ≥ 3`, witness at
root dimension `d - 1 = 2 * k`.  G5 only constructs the steps. -/
theorem propagate {m : Nat} [NeZero m]
    (step : ∀ k, 3 ≤ k → GrowthStep (2 * k) m) :
    HEDWitness 6 m → ∀ d, 7 ≤ d → d % 2 = 1 → FinalMarkedTarget d m := by
  intro base d hd hodd
  obtain ⟨j, rfl⟩ : ∃ j, d = 2 * (j + 3) + 1 := ⟨(d - 7) / 2, by omega⟩
  exact (iterateSteps step base j).toMarkedTarget

/-- Payload form of the driver (marked target + real-content evidence). -/
theorem propagatePayload {m : Nat} [NeZero m]
    (step : ∀ k, 3 ≤ k → GrowthStep (2 * k) m) :
    HEDWitness 6 m → ∀ d, 7 ≤ d → d % 2 = 1 → FinalMarkedPayload d m := by
  intro base d hd hodd
  obtain ⟨j, rfl⟩ : ∃ j, d = 2 * (j + 3) + 1 := ⟨(d - 7) / 2, by omega⟩
  exact (iterateSteps step base j).toMarkedPayload

/-! ## Sanity (shape-level only; the heavy `(7, 4)/(7, 6)` certificates are G3)

The chain-field example below checks exactly the gate report's label-chart /
carrier arithmetic clauses for the chained `7 → 9` window: chart
`ZMod 9 \ {0, 1}` (old labels embedded as `i + 2`), carrier `{3, 4, 6}`
inside the chart and disjoint from the row supports.  Row values are
shape-level placeholders; the certified values land in G3. -/

/-- Chained `7 → 9` chart/carrier arithmetic sanity (`check_hed_clauses.py`
chain-datum bookkeeping items 2 and 5): all six chain clauses close by
`decide` on the paper's chained chart. -/
def chainedChartShapeExample : ChainFields 6 :=
  ChainFields.ofBool
    (newLabels := (0, 1))
    (oldLabel := fun i => ((i : Nat) : ZMod 9) + 2)
    (rows := fun r =>
      if r = 0 then
        { support := [0, 2, 7, 5], leafLine := (0, 2), quotientGen := (7, 5)
          oldGens := [(7, 5)], phase := 1, delta := 1 }
      else
        { support := [1, 2, 0, 8], leafLine := (1, 2), quotientGen := (0, 8)
          oldGens := [(0, 8)], phase := 5, delta := 1 })
    (carrier := ![3, 4, 6])
    (by decide)

example : chainedChartShapeExample.guideCenters 0 = [0, 1, 2] := by decide

example {n m : Nat} [NeZero m] (w : HEDWitness n m) :
    FinalMarkedTarget (n + 1) m :=
  w.toMarkedTarget

example {n m : Nat} [NeZero m] (w : HEDWitness n m) :
    FinalMarkedPayload (n + 1) m :=
  w.toMarkedPayload

/-- Driver shape-check: a step family plus the dimension-7 base reaches the
first chained target `d = 9` (and `d = 11`, the first paired one). -/
example {m : Nat} [NeZero m]
    (step : ∀ k, 3 ≤ k → GrowthStep (2 * k) m) (base : HEDWitness 6 m) :
    FinalMarkedTarget 9 m ∧ FinalMarkedTarget 11 m :=
  ⟨propagate step base 9 (by omega) (by omega),
    propagate step base 11 (by omega) (by omega)⟩

end HEDWitness
end V28Hard
end EvenV11
