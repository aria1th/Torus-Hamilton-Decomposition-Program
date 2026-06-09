import EvenV11.TerminalA2LowMod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

/-!
# Hard slot H6 (E3+E4): parametric endpoint port room

The child endpoint section is `E = Y × Q × Z` with `Y` the (abstract) parent
return section, `Q = (ℤ/m)²` the terminal A2 block and `Z = (ℤ/m)^{b-1}` the
minus-lane coordinates.  This file formalizes:

* **E3 core** — the reset common-image equation
  (`lem:endpoint-reset-common-image`): with reset rows
  `r₀ = (c_*, q_R, z_R)` and `r₁ = (c_*, q_R, z_R + δ_{lane₀} − δ_{lane₁})`
  one has `r₀ + δ_{lane₀} = r₁ + δ_{lane₁} = (c_*, q_R, z_R + δ_{lane₀})`,
  the addition acting only on the `Z` component.
* **E3 separation skeleton** — the endpoint row list
  `𝒫 = (x₀,x₁,x₂, r₀,r₁, c₁,…,c_{b−1}) ∈ E^{b+4}` with pairwise-distinct
  sites, packaged as an injective site map on `Fin 3 ⊕ Fin 2 ⊕ Fin (b-1)`.
* **E4** — the renewal-cylinder capacity `2b+4 < m^{b-1}` (for `4 ≤ b`,
  `4 ≤ m`) and the role split of the `2b+4` reserved successors: 3 next
  terminal exchanges + `2b` next completion switches + 1 next endpoint site.
  This step *consumes* the `b-1` completion sites `c_j` of dimension `b` and
  *grants* `2b` completion slots to the next dimension `d' = 2b+1` (which has
  `d'-1 = 2b` of them); the reserve count is `d'+3 = 2b+4`.
-/

namespace EvenV11
namespace V28Hard
namespace EndpointPortRoom

/-! ## Part A — section type and the reset common image (E3 core) -/

/-- Minus-lane coordinates of the endpoint chart: `Z = (ℤ/m)^{b-1}`. -/
abbrev LaneZ (b m : Nat) := Fin (b - 1) → ZMod m

/-- Child endpoint section `E = Y × Q × Z`: parent return section,
terminal A2 block, minus-lane coordinates. -/
abbrev EndpointSection (Y : Type*) (b m : Nat) :=
  Y × TerminalA2LowMod.TerminalQ m × LaneZ b m

/-- Unit vector in minus lane `j`: adds `1` to coordinate `j` of `Z`. -/
def laneDelta {b m : Nat} (j : Fin (b - 1)) : LaneZ b m :=
  fun i => if i = j then 1 else 0

@[simp] theorem laneDelta_apply_self {b m : Nat} (j : Fin (b - 1)) :
    laneDelta (b := b) (m := m) j j = 1 :=
  if_pos rfl

@[simp] theorem laneDelta_apply_of_ne {b m : Nat} {i j : Fin (b - 1)}
    (h : i ≠ j) : laneDelta (b := b) (m := m) j i = 0 :=
  if_neg h

/-- Distinct lanes give distinct unit vectors (this needs `1 < m`, i.e.
`(1 : ZMod m) ≠ 0`). -/
theorem laneDelta_ne_laneDelta {b m : Nat} (hm : 1 < m) {j j' : Fin (b - 1)}
    (h : j ≠ j') : laneDelta (b := b) (m := m) j ≠ laneDelta j' := by
  haveI : Fact (1 < m) := ⟨hm⟩
  intro he
  have h1 := congrFun he j
  rw [laneDelta_apply_self, laneDelta_apply_of_ne h] at h1
  exact one_ne_zero h1

/-- Reset data of the endpoint row list: selector base `c_* : Y`, terminal
block value `q_R`, lane base point `z_R`, and the two distinct minus lanes
(the paper's `p₁⁻`, `p₂⁻`) used by the reset rows. -/
structure ResetPair (Y : Type*) (b m : Nat) where
  /-- Selector base `c_*` in the parent return section. -/
  selector : Y
  /-- Terminal A2 block value `q_R` shared by both reset rows. -/
  qR : TerminalA2LowMod.TerminalQ m
  /-- Minus-lane base point `z_R`. -/
  zR : LaneZ b m
  /-- First reset lane (the paper's `p₁⁻`). -/
  lane0 : Fin (b - 1)
  /-- Second reset lane (the paper's `p₂⁻`). -/
  lane1 : Fin (b - 1)
  /-- The two reset lanes are distinct. -/
  lanes_ne : lane0 ≠ lane1

namespace ResetPair

variable {Y : Type*} {b m : Nat} (R : ResetPair Y b m)

/-- First reset row `r₀ = (c_*, q_R, z_R)`. -/
def r0 : EndpointSection Y b m := (R.selector, R.qR, R.zR)

/-- Second reset row `r₁ = (c_*, q_R, z_R + δ_{lane₀} − δ_{lane₁})`
(the paper's `z_R + ε₁⁻ − ε₂⁻`). -/
def r1 : EndpointSection Y b m :=
  (R.selector, R.qR, R.zR + laneDelta R.lane0 - laneDelta R.lane1)

/-- Common image `I = (c_*, q_R, z_R + δ_{lane₀})` of the two reset rows. -/
def commonImage : EndpointSection Y b m :=
  (R.selector, R.qR, R.zR + laneDelta R.lane0)

/-- `r₀ + δ_{lane₀} = I` (addition only in the `Z` component). -/
theorem r0_image :
    (R.r0.1, R.r0.2.1, R.r0.2.2 + laneDelta R.lane0) = R.commonImage :=
  rfl

/-- `r₁ + δ_{lane₁} = I`: indeed
`z_R + δ_{lane₀} − δ_{lane₁} + δ_{lane₁} = z_R + δ_{lane₀}`. -/
theorem r1_image :
    (R.r1.1, R.r1.2.1, R.r1.2.2 + laneDelta R.lane1) = R.commonImage := by
  change (R.selector, R.qR,
      R.zR + laneDelta R.lane0 - laneDelta R.lane1 + laneDelta R.lane1)
    = (R.selector, R.qR, R.zR + laneDelta R.lane0)
  rw [sub_add_cancel]

/-- Reset common-image equation (`lem:endpoint-reset-common-image`): the two
reset rows reach the same image `I = (c_*, q_R, z_R + δ_{lane₀})`, row `r₀`
through lane `lane₀` and row `r₁` through lane `lane₁`. -/
theorem common_image_eq :
    (R.r0.1, R.r0.2.1, R.r0.2.2 + laneDelta R.lane0) = R.commonImage ∧
    (R.r1.1, R.r1.2.1, R.r1.2.2 + laneDelta R.lane1) = R.commonImage :=
  ⟨R.r0_image, R.r1_image⟩

/-- The two reset rows are distinct (needs `1 < m`). -/
theorem r0_ne_r1 (hm : 1 < m) : R.r0 ≠ R.r1 := by
  haveI : Fact (1 < m) := ⟨hm⟩
  intro h
  have h3 : R.zR = R.zR + laneDelta R.lane0 - laneDelta R.lane1 :=
    congrArg (fun s : EndpointSection Y b m => s.2.2) h
  have h4 := congrFun h3 R.lane0
  rw [Pi.sub_apply, Pi.add_apply, laneDelta_apply_self,
    laneDelta_apply_of_ne R.lanes_ne, sub_zero] at h4
  exact one_ne_zero (left_eq_add.mp h4)

/-- The first reset row differs from the common image (needs `1 < m`). -/
theorem r0_ne_commonImage (hm : 1 < m) : R.r0 ≠ R.commonImage := by
  haveI : Fact (1 < m) := ⟨hm⟩
  intro h
  have h3 : R.zR = R.zR + laneDelta R.lane0 :=
    congrArg (fun s : EndpointSection Y b m => s.2.2) h
  have h4 := congrFun h3 R.lane0
  rw [Pi.add_apply, laneDelta_apply_self] at h4
  exact one_ne_zero (left_eq_add.mp h4)

/-- The second reset row differs from the common image (needs `1 < m`). -/
theorem r1_ne_commonImage (hm : 1 < m) : R.r1 ≠ R.commonImage := by
  haveI : Fact (1 < m) := ⟨hm⟩
  intro h
  have h3 : R.zR + laneDelta R.lane0 - laneDelta R.lane1
      = R.zR + laneDelta R.lane0 :=
    congrArg (fun s : EndpointSection Y b m => s.2.2) h
  have h4 := congrFun h3 R.lane1
  rw [Pi.sub_apply, Pi.add_apply, laneDelta_apply_self,
    laneDelta_apply_of_ne (Ne.symm R.lanes_ne), add_zero] at h4
  exact one_ne_zero (sub_eq_self.mp h4)

end ResetPair

/-! ## Part B — the endpoint row list with disjoint supports (E3 skeleton)

The list `𝒫 = (x₀,x₁,x₂, r₀,r₁, c₁,…,c_{b−1})` of `3 + 2 + (b-1) = b+4`
endpoint sites, recorded with the paper's pairwise-distinctness
requirements.  The actual ribbon supports are attached later (E5); what E5
consumes is the injective site bookkeeping `EndpointRowList.site`. -/

/-- Endpoint row list: 3 exchange sites, the reset pair, and `b-1`
completion sites, pairwise distinct. -/
structure EndpointRowList (Y : Type*) (b m : Nat) where
  /-- The three exchange sites `x₀, x₁, x₂`. -/
  exchangeSite : Fin 3 → EndpointSection Y b m
  /-- The reset pair `r₀, r₁` with its lane data. -/
  resetPair : ResetPair Y b m
  /-- The `b-1` completion sites `c₁, …, c_{b−1}`. -/
  completionSite : Fin (b - 1) → EndpointSection Y b m
  /-- The exchange sites are pairwise distinct. -/
  exchange_injective : Function.Injective exchangeSite
  /-- The completion sites are pairwise distinct. -/
  completion_injective : Function.Injective completionSite
  /-- No exchange site coincides with the first reset row. -/
  exchange_ne_reset0 : ∀ i, exchangeSite i ≠ resetPair.r0
  /-- No exchange site coincides with the second reset row. -/
  exchange_ne_reset1 : ∀ i, exchangeSite i ≠ resetPair.r1
  /-- No exchange site coincides with a completion site. -/
  exchange_ne_completion : ∀ i j, exchangeSite i ≠ completionSite j
  /-- The first reset row coincides with no completion site. -/
  reset0_ne_completion : ∀ j, resetPair.r0 ≠ completionSite j
  /-- The second reset row coincides with no completion site. -/
  reset1_ne_completion : ∀ j, resetPair.r1 ≠ completionSite j

/-- The site index set has `3 + 2 + (b-1) = b + 4` elements (for `1 ≤ b`). -/
theorem siteIndex_card {b : Nat} (hb : 1 ≤ b) :
    Fintype.card (Fin 3 ⊕ Fin 2 ⊕ Fin (b - 1)) = b + 4 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

namespace EndpointRowList

variable {Y : Type*} {b m : Nat} (L : EndpointRowList Y b m)

/-- The two reset sites, indexed by `Fin 2`. -/
def resetSite : Fin 2 → EndpointSection Y b m :=
  fun k => if k = 0 then L.resetPair.r0 else L.resetPair.r1

@[simp] theorem resetSite_zero : L.resetSite 0 = L.resetPair.r0 :=
  if_pos rfl

@[simp] theorem resetSite_one : L.resetSite 1 = L.resetPair.r1 :=
  if_neg (by decide)

/-- The combined map of all `b+4` endpoint sites, indexed by
`Fin 3 ⊕ Fin 2 ⊕ Fin (b-1)`: exchanges, then resets, then completions. -/
def site : Fin 3 ⊕ Fin 2 ⊕ Fin (b - 1) → EndpointSection Y b m :=
  Sum.elim L.exchangeSite (Sum.elim L.resetSite L.completionSite)

/-- The two reset sites are distinct (needs `1 < m`). -/
theorem resetSite_injective (hm : 1 < m) : Function.Injective L.resetSite := by
  have h01 := L.resetPair.r0_ne_r1 hm
  intro k k' h
  fin_cases k <;> fin_cases k' <;>
    first
      | rfl
      | exact absurd h h01
      | exact absurd h.symm h01

/-- All `b+4` endpoint sites are pairwise distinct: the combined site map
is injective (needs `1 < m` for `r₀ ≠ r₁`). -/
theorem site_injective (hm : 1 < m) : Function.Injective L.site := by
  have hres := L.resetSite_injective hm
  have her : ∀ i k, L.exchangeSite i ≠ L.resetSite k := by
    intro i k
    fin_cases k
    · exact L.exchange_ne_reset0 i
    · exact L.exchange_ne_reset1 i
  have hrc : ∀ k j, L.resetSite k ≠ L.completionSite j := by
    intro k j
    fin_cases k
    · exact L.reset0_ne_completion j
    · exact L.reset1_ne_completion j
  rintro (i | k | j) (i' | k' | j') h
  · exact congrArg Sum.inl (L.exchange_injective h)
  · exact absurd h (her i k')
  · exact absurd h (L.exchange_ne_completion i j')
  · exact absurd h.symm (her i' k)
  · exact congrArg (Sum.inr ∘ Sum.inl) (hres h)
  · exact absurd h (hrc k j')
  · exact absurd h.symm (L.exchange_ne_completion i' j)
  · exact absurd h.symm (hrc k' j)
  · exact congrArg (Sum.inr ∘ Sum.inr) (L.completion_injective h)

end EndpointRowList

/-! ## Part C — renewal capacity and role split (E4) -/

/-- Capacity over base `4`: `2b + 4 < 4^{b-1}` for `b ≥ 4`. -/
theorem two_mul_add_four_lt_four_pow {b : Nat} (hb : 4 ≤ b) :
    2 * b + 4 < 4 ^ (b - 1) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn1 : n - 1 + 1 = n := by omega
    have hpow : 4 ^ n = 4 * 4 ^ (n - 1) := by
      calc 4 ^ n = 4 ^ (n - 1 + 1) := by rw [hn1]
        _ = 4 ^ (n - 1) * 4 := pow_succ 4 (n - 1)
        _ = 4 * 4 ^ (n - 1) := Nat.mul_comm _ _
    have hpos : 1 ≤ 4 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    simp only [Nat.add_sub_cancel]
    omega

/-- Renewal capacity: `2b + 4 < m^{b-1}` for `b ≥ 4`, `m ≥ 4`. -/
theorem two_mul_add_four_lt_pow {b m : Nat} (hb : 4 ≤ b) (hm : 4 ≤ m) :
    2 * b + 4 < m ^ (b - 1) :=
  lt_of_lt_of_le (two_mul_add_four_lt_four_pow hb)
    (Nat.pow_le_pow_left hm (b - 1))

/-- The renewal cylinder `{u_*} × {q_*} × Z` has `m^{b-1}` states. -/
theorem laneZ_card (b m : Nat) [NeZero m] :
    Fintype.card (LaneZ b m) = m ^ (b - 1) := by
  simp only [LaneZ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- Capacity of the renewal cylinder: it holds strictly more than the
`2b + 4` reserved successor values (for `b ≥ 4`, `m ≥ 4`). -/
theorem renewal_capacity {b m : Nat} [NeZero m] (hb : 4 ≤ b) (hm : 4 ≤ m) :
    2 * b + 4 < Fintype.card (LaneZ b m) := by
  rw [laneZ_card]
  exact two_mul_add_four_lt_pow hb hm

/-- Role split of the `2b+4` reserved successor values at the renewal step
to dimension `d' = 2b+1`: 3 next terminal exchanges, `2b = d'-1` next
completion switches, and 1 next endpoint site (`d'+3 = 2b+4` in total). -/
inductive RenewalRole (b : Nat) where
  /-- One of the 3 next terminal exchange slots. -/
  | exchange (i : Fin 3)
  /-- One of the `2b = d'-1` next completion-switch slots granted to the
  next dimension `d' = 2b+1`. -/
  | completion (j : Fin (2 * b))
  /-- The single next endpoint site. -/
  | nextReserve
  deriving DecidableEq

namespace RenewalRole

/-- Canonical index of a renewal role inside `Fin (2b+4)`:
exchanges first, then completions, then the next endpoint site. -/
def index {b : Nat} : RenewalRole b → Fin (2 * b + 4)
  | .exchange i => ⟨i.val, by have := i.isLt; omega⟩
  | .completion j => ⟨3 + j.val, by have := j.isLt; omega⟩
  | .nextReserve => ⟨2 * b + 3, by omega⟩

/-- The role indexing is injective. -/
theorem index_injective {b : Nat} :
    Function.Injective (index (b := b)) := by
  intro r r' h
  cases r with
  | exchange i =>
    cases r' with
    | exchange i' =>
      simp only [index, Fin.mk.injEq] at h
      exact congrArg RenewalRole.exchange (Fin.ext h)
    | completion j' =>
      simp only [index, Fin.mk.injEq] at h
      exact absurd h (by have := i.isLt; omega)
    | nextReserve =>
      simp only [index, Fin.mk.injEq] at h
      exact absurd h (by have := i.isLt; omega)
  | completion j =>
    cases r' with
    | exchange i' =>
      simp only [index, Fin.mk.injEq] at h
      exact absurd h (by have := i'.isLt; omega)
    | completion j' =>
      simp only [index, Fin.mk.injEq] at h
      exact congrArg RenewalRole.completion (Fin.ext (by omega))
    | nextReserve =>
      simp only [index, Fin.mk.injEq] at h
      exact absurd h (by have := j.isLt; omega)
  | nextReserve =>
    cases r' with
    | exchange i' =>
      simp only [index, Fin.mk.injEq] at h
      exact absurd h.symm (by have := i'.isLt; omega)
    | completion j' =>
      simp only [index, Fin.mk.injEq] at h
      exact absurd h.symm (by have := j'.isLt; omega)
    | nextReserve => rfl

end RenewalRole

/-- The renewal roles, counted: `RenewalRole b ≃ Fin 3 ⊕ Fin (2b) ⊕ Fin 1`. -/
def renewalRoleEquivSum (b : Nat) :
    RenewalRole b ≃ (Fin 3 ⊕ Fin (2 * b) ⊕ Fin 1) where
  toFun
    | .exchange i => .inl i
    | .completion j => .inr (.inl j)
    | .nextReserve => .inr (.inr 0)
  invFun
    | .inl i => .exchange i
    | .inr (.inl j) => .completion j
    | .inr (.inr _) => .nextReserve
  left_inv r := by cases r <;> rfl
  right_inv s := by
    rcases s with i | j | x
    · rfl
    · rfl
    · exact congrArg (Sum.inr ∘ Sum.inr) (Subsingleton.elim _ _)

instance (b : Nat) : Fintype (RenewalRole b) :=
  Fintype.ofEquiv _ (renewalRoleEquivSum b).symm

/-- Count of the renewal roles: `3 + 2b + 1 = 2b + 4`. -/
theorem renewalRole_card (b : Nat) :
    Fintype.card (RenewalRole b) = 2 * b + 4 := by
  rw [Fintype.card_congr (renewalRoleEquivSum b)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Base-`m` digit placement of the `2b+4` reserved indices in the
minus-lane coordinates `Z = (ℤ/m)^{b-1}` of the renewal cylinder. -/
def laneDigits {b m : Nat} : Fin (2 * b + 4) → LaneZ b m :=
  fun k i => ((k.val / m ^ i.val % m : Nat) : ZMod m)

/-- The digit placement is injective: since `2b+4 < m^{b-1}` (for `b ≥ 4`,
`m ≥ 4`), the `b-1` base-`m` digits determine the index. -/
theorem laneDigits_injective {b m : Nat} (hb : 4 ≤ b) (hm : 4 ≤ m) :
    Function.Injective (laneDigits (b := b) (m := m)) := by
  intro k k' h
  have hdig : ∀ n, n < b - 1 → k.val / m ^ n % m = k'.val / m ^ n % m := by
    intro n hn
    have hfun : ((k.val / m ^ n % m : Nat) : ZMod m)
        = ((k'.val / m ^ n % m : Nat) : ZMod m) :=
      congrFun h (⟨n, hn⟩ : Fin (b - 1))
    have h1 : k.val / m ^ n % m < m := Nat.mod_lt _ (by omega)
    have h2 : k'.val / m ^ n % m < m := Nat.mod_lt _ (by omega)
    have hval := congrArg ZMod.val hfun
    rwa [ZMod.val_cast_of_lt h1, ZMod.val_cast_of_lt h2] at hval
  have hmod : ∀ j, j ≤ b - 1 → k.val % m ^ j = k'.val % m ^ j := by
    intro j
    induction j with
    | zero => intro _; simp [Nat.mod_one]
    | succ n ih =>
      intro hj
      have hrec := ih (by omega)
      rw [pow_succ, Nat.mod_mul, Nat.mod_mul, hrec, hdig n (by omega)]
  have hcap := two_mul_add_four_lt_pow hb hm
  have hk : k.val % m ^ (b - 1) = k.val :=
    Nat.mod_eq_of_lt (by have := k.isLt; omega)
  have hk' : k'.val % m ^ (b - 1) = k'.val :=
    Nat.mod_eq_of_lt (by have := k'.isLt; omega)
  have := hmod (b - 1) le_rfl
  rw [hk, hk'] at this
  exact Fin.ext this

/-- Placement of the renewal roles in the renewal cylinder
`{u_*} × {q_*} × Z`: constant parent/terminal components, base-`m` digit
encoding in the minus lanes. -/
def renewalSlot {Y : Type*} {b m : Nat} (uStar : Y)
    (qStar : TerminalA2LowMod.TerminalQ m) :
    RenewalRole b → EndpointSection Y b m :=
  fun r => (uStar, qStar, laneDigits (RenewalRole.index r))

/-- The `2b+4` renewal slots are pairwise distinct successor values inside
the renewal cylinder (for `b ≥ 4`, `m ≥ 4`). -/
theorem renewalSlot_injective {Y : Type*} {b m : Nat} (hb : 4 ≤ b)
    (hm : 4 ≤ m) (uStar : Y) (qStar : TerminalA2LowMod.TerminalQ m) :
    Function.Injective (renewalSlot (b := b) uStar qStar) := by
  intro r r' h
  have hz : laneDigits (b := b) (m := m) (RenewalRole.index r)
      = laneDigits (RenewalRole.index r') :=
    congrArg (fun s : EndpointSection Y b m => s.2.2) h
  exact RenewalRole.index_injective (laneDigits_injective hb hm hz)

end EndpointPortRoom
end V28Hard
end EvenV11
