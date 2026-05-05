import RoundComposite.BaseTailGeometry

namespace RoundComposite
namespace Concrete
namespace BaseTail
namespace Trades

/--
Primitive residue-unit side conditions used by the active local-trade layer.

The condition is intentionally phrased over an arbitrary residue specification
so the paper-facing endpoints can talk about row/column-compatible scheduling
before committing to a concrete active symboling.
-/
def PrimitiveResidueSpec {b m T : Nat}
    (hT : 2 ≤ T) (R : ActiveHall.ResidueSpec m T (Fin (b + T))) : Prop :=
  (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
    (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit (R.target c σ - R.target c ⟨1, by omega⟩))

/--
Canonical residue schedule carried by an active-block cylinder.

The schedule uses the active block sizes as unit residues in symbol `0`, their
negatives in symbol `1`, and zero thereafter.  The active-block degree and
total-sum identities make this row/column compatible.
-/
noncomputable def activeBlockResidueSpec {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) :
    ActiveHall.ResidueSpec m T (Fin (b + T)) :=
  ActiveHall.universalUnitResidueSpecOfTwoLe m (b + T) T
    (fun c => (D.activeBlock c : ZMod m))

@[simp] theorem activeBlockResidueSpec_target_zero {b m T : Nat}
    [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} (D : ActiveBlockData Cyl)
    (c : Fin (b + T)) (h0 : 0 < T) :
    (activeBlockResidueSpec D).target c ⟨0, h0⟩ =
      (D.activeBlock c : ZMod m) := by
  simp [activeBlockResidueSpec, ActiveHall.universalUnitResidueSpecOfTwoLe]

@[simp] theorem activeBlockResidueSpec_target_one {b m T : Nat}
    [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} (D : ActiveBlockData Cyl)
    (c : Fin (b + T)) (h1 : 1 < T) :
    (activeBlockResidueSpec D).target c ⟨1, h1⟩ =
      -((D.activeBlock c : Nat) : ZMod m) := by
  simp [activeBlockResidueSpec, ActiveHall.universalUnitResidueSpecOfTwoLe]

theorem activeBlockResidueSpec_target_of_two_le {b m T : Nat}
    [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} (D : ActiveBlockData Cyl)
    (c : Fin (b + T)) {σ : Fin T} (hσ : 2 ≤ σ.val) :
    (activeBlockResidueSpec D).target c σ = 0 := by
  have h0 : σ.val ≠ 0 := by omega
  have h1 : σ.val ≠ 1 := by omega
  simp [activeBlockResidueSpec, ActiveHall.universalUnitResidueSpecOfTwoLe,
    h0, h1]

theorem symbolingWithResidues_activeBlockResidueSpec_of_permuteResidueSpec_target_eq
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    {Φ : ActiveHall.Symboling Cyl.incidence}
    (D : ActiveBlockData Cyl)
    (hΦ : Φ.HasResidues R)
    (x₀ : Shared.TorusVertex (b + 1) m)
    (π : Equiv.Perm (Fin T))
    (hTarget :
      ∀ c σ,
        (Φ.permuteResidueSpec R x₀ π).target c σ =
          (activeBlockResidueSpec D).target c σ) :
    ActiveHall.SymbolingWithResidues Cyl.incidence
      (activeBlockResidueSpec D) := by
  have hR :
      Φ.permuteResidueSpec R x₀ π = activeBlockResidueSpec D := by
    have htarget :
        (Φ.permuteResidueSpec R x₀ π).target =
          (activeBlockResidueSpec D).target := by
      funext c σ
      exact hTarget c σ
    cases hperm : Φ.permuteResidueSpec R x₀ π with
    | mk targetPerm =>
        cases hblock : activeBlockResidueSpec D with
        | mk targetBlock =>
            have htarget' : targetPerm = targetBlock := by
              rw [hperm, hblock] at htarget
              exact htarget
            cases htarget'
            rfl
  simpa [hR] using
    ActiveHall.symbolingWithResidues_of_permuteAt_hasResidues
      hΦ x₀ π

/--
Target equality for one-site permutation correction from a pre-correction
formula.

This is the algebraic form produced by a local trade that reserves one site for
the final symbol permutation: the pre-correction target is the canonical target
plus the old local contribution minus the permuted local contribution.
-/
theorem permuteResidueSpec_target_eq_activeBlockResidueSpec_of_preTarget
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    {Φ : ActiveHall.Symboling Cyl.incidence}
    (D : ActiveBlockData Cyl)
    (x₀ : Shared.TorusVertex (b + 1) m)
    (π : Equiv.Perm (Fin T))
    (hPre :
      ∀ c σ,
        R.target c σ =
          (activeBlockResidueSpec D).target c σ
            + (if Φ.color x₀ σ = c then (1 : ZMod m) else 0)
            - (if Φ.color x₀ (π σ) = c then (1 : ZMod m) else 0)) :
    ∀ c σ,
      (Φ.permuteResidueSpec R x₀ π).target c σ =
        (activeBlockResidueSpec D).target c σ := by
  intro c σ
  rw [ActiveHall.Symboling.permuteResidueSpec_target, hPre c σ]
  abel

/--
Canonical active-block residue correction by one local permutation, phrased in
the three cases of the canonical target schedule.

This is the form expected from the reserved local-trade site: symbol `0`
receives the active-block unit, symbol `1` receives its negative, and all
remaining symbols receive zero.
-/
theorem symbolingWithResidues_activeBlockResidueSpec_of_permuteResidueSpec_target_cases
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    {Φ : ActiveHall.Symboling Cyl.incidence}
    (D : ActiveBlockData Cyl)
    (hT : 2 ≤ T)
    (hΦ : Φ.HasResidues R)
    (x₀ : Shared.TorusVertex (b + 1) m)
    (π : Equiv.Perm (Fin T))
    (hZero :
      ∀ c : Fin (b + T),
        (Φ.permuteResidueSpec R x₀ π).target c ⟨0, by omega⟩ =
          (D.activeBlock c : ZMod m))
    (hOne :
      ∀ c : Fin (b + T),
        (Φ.permuteResidueSpec R x₀ π).target c ⟨1, by omega⟩ =
          -((D.activeBlock c : Nat) : ZMod m))
    (hTail :
      ∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        (Φ.permuteResidueSpec R x₀ π).target c σ = 0) :
    ActiveHall.SymbolingWithResidues Cyl.incidence
      (activeBlockResidueSpec D) := by
  exact
    symbolingWithResidues_activeBlockResidueSpec_of_permuteResidueSpec_target_eq
      D hΦ x₀ π (by
        intro c σ
        by_cases hσ0 : σ.val = 0
        · have hσ : σ = ⟨0, by omega⟩ := Fin.ext hσ0
          rw [hσ]
          simpa using hZero c
        · by_cases hσ1 : σ.val = 1
          · have hσ : σ = ⟨1, by omega⟩ := Fin.ext hσ1
            rw [hσ]
            simpa using hOne c
          · have hσ2 : 2 ≤ σ.val := by omega
            rw [hTail c σ hσ2,
              activeBlockResidueSpec_target_of_two_le D c hσ2])

/--
Direct active-block residue scheduler.

This is the v7.3 replacement surface for the old count-matrix feasibility
stage: on an active-block cylinder, choose a row/column-compatible primitive
residue target without first producing a Hall count matrix.
-/
def ActiveBlockResidueScheduleGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      (hT : 2 ≤ T) →
        ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
          R.RowCompatible Cyl.incidence ∧
          R.ColCompatible Cyl.incidence ∧
          PrimitiveResidueSpec hT R

/--
Direct active-block local-symbol trade endpoint.

Given a compatible primitive residue target on an active-block cylinder, local
trades directly realize a symboling with those residues.
-/
def ActiveBlockLocalSymbolTradeGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T)
    (R : ActiveHall.ResidueSpec m T (Fin (b + T))),
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
      PrimitiveResidueSpec hT R →
        ActiveHall.SymbolingWithResidues Cyl.incidence R

/--
Combined direct residue-trade realization endpoint.  This packages the
scheduler and local trade result as the object the downstream active symboling
adapter consumes.
-/
def ActiveBlockResidueTradeRealizationGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      (hT : 2 ≤ T) →
        ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
          R.RowCompatible Cyl.incidence ∧
          R.ColCompatible Cyl.incidence ∧
          PrimitiveResidueSpec hT R ∧
          ActiveHall.SymbolingWithResidues Cyl.incidence R

/--
Successor-scoped active-block residue scheduler.

This is the narrow v7.3 proof surface.  Unlike
`ActiveBlockResidueScheduleGoal`, it only asks for residue scheduling under the
small-modulus successor hypotheses and packet/slack data that produce the
base-tail cylinder.
-/
def SuccessorActiveBlockResidueScheduleGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      (hT : 2 ≤ T) →
        ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
          R.RowCompatible Cyl.incidence ∧
          R.ColCompatible Cyl.incidence ∧
          PrimitiveResidueSpec hT R

/--
Successor-scoped local-symbol trade endpoint.

The local trade construction is only required on the actual successor
active-block cylinders, with the same packet/slack context as the scheduler.
-/
def SuccessorActiveBlockLocalSymbolTradeGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      (R : ActiveHall.ResidueSpec m T (Fin (b + T))) →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
      PrimitiveResidueSpec hT R →
        ActiveHall.SymbolingWithResidues Cyl.incidence R

/--
Paper-facing active residue scheduling theorem for successor cylinders.

This is the Lean endpoint corresponding to the v7.6 active-residue scheduling
statement: every row/column compatible residue target on the successor
active-incidence cylinder is realized directly by local symbol trades.  The
older `SuccessorActiveBlockLocalSymbolTradeGoal` is the primitive-residue
specialization consumed by the prefix-count tail.
-/
def SuccessorActiveBlockCompatibleResidueSchedulingGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      (R : ActiveHall.ResidueSpec m T (Fin (b + T))) →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
        ActiveHall.SymbolingWithResidues Cyl.incidence R

/--
Reservoir swap-schedule endpoint for compatible successor residues.

This is the concrete finite-schedule layer below
`SuccessorActiveBlockCompatibleResidueSchedulingGoal`: it supplies an initial
residue-realizing symboling and a finite list of local swaps whose induced
residue specification is exactly the requested compatible target.
-/
def SuccessorActiveBlockReservoirSwapScheduleGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      (R : ActiveHall.ResidueSpec m T (Fin (b + T))) →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
        ∃ R₀ : ActiveHall.ResidueSpec m T (Fin (b + T)),
          ∃ Φ : ActiveHall.Symboling Cyl.incidence,
            Φ.HasResidues R₀ ∧
              ∃ moves :
                List
                  (ActiveHall.Symboling.SwapMove
                    (Shared.TorusVertex (b + 1) m) T),
                Φ.applySwapResidueSpecs R₀ moves = R

/--
Reservoir swap-schedule endpoint with the initial residues inferred from the
initial symboling itself.

This is the form most convenient for the constructive reservoir proof: after
choosing an initial symboling and a finite swap list, the initial residue
specification is just `Φ.residueSpec`.
-/
def SuccessorActiveBlockInitialReservoirSwapScheduleGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      (R : ActiveHall.ResidueSpec m T (Fin (b + T))) →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
        ∃ Φ : ActiveHall.Symboling Cyl.incidence,
          ∃ moves :
            List
              (ActiveHall.Symboling.SwapMove
                (Shared.TorusVertex (b + 1) m) T),
            Φ.applySwapResidueSpecs (Φ.residueSpec (m := m)) moves = R

/--
Reservoir endpoint specialized to paper-style `0 ↔ τ` local trades.

This is the direct Lean shape of the v7.6 reservoir schedule: the remaining
constructive proof only has to choose an initial symboling and a finite list of
zero-symbol trades.  Expanding those trades to generic swaps is bookkeeping.
-/
def SuccessorActiveBlockZeroReservoirSwapScheduleGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      (R : ActiveHall.ResidueSpec m T (Fin (b + T))) →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
        ∃ Φ : ActiveHall.Symboling Cyl.incidence,
          ∃ moves :
            List
              (ActiveHall.Symboling.ZeroSwapMove
                (Shared.TorusVertex (b + 1) m) T),
            Φ.applySwapResidueSpecs (Φ.residueSpec (m := m))
              (ActiveHall.Symboling.zeroSwapMoves
                (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT) moves) = R

/--
Strict paper-style reservoir endpoint where every scheduled `0 ↔ τ` local
trade carries the proof that `τ ≠ 0`.
-/
def SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      (R : ActiveHall.ResidueSpec m T (Fin (b + T))) →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
        ∃ Φ : ActiveHall.Symboling Cyl.incidence,
          ∃ moves :
            List
              (ActiveHall.Symboling.NonzeroZeroSwapMove
                (Shared.TorusVertex (b + 1) m) T),
            Φ.applySwapResidueSpecs (Φ.residueSpec (m := m))
              (ActiveHall.Symboling.nonzeroZeroSwapMoves
                (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT) moves) = R

/--
Canonical-only strict reservoir endpoint.

This is the weaker surface actually needed by the successor closure: the
finite `0 ↔ τ`, `τ ≠ 0`, schedule only has to realize the canonical active-block
residue target, not every compatible residue matrix.
-/
def SuccessorActiveBlockCanonicalNonzeroZeroReservoirSwapScheduleGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
        ∃ Φ : ActiveHall.Symboling Cyl.incidence,
          ∃ moves :
            List
              (ActiveHall.Symboling.NonzeroZeroSwapMove
                (Shared.TorusVertex (b + 1) m) T),
            Φ.applySwapResidueSpecs (Φ.residueSpec (m := m))
              (ActiveHall.Symboling.nonzeroZeroSwapMoves
                (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT) moves) =
                  activeBlockResidueSpec D

def nonzeroZeroSwapMovesOfTwoLe {X : Type*} {T : Nat} (hT : 2 ≤ T)
    (moves : List (ActiveHall.Symboling.NonzeroZeroSwapMove X T)) :
    List (ActiveHall.Symboling.SwapMove X T) :=
  ActiveHall.Symboling.nonzeroZeroSwapMoves
    (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT) moves

def nonzeroZeroTradeDeltaSumOfTwoLe {m T : Nat} {X C : Type*}
    [DecidableEq C] (hT : 2 ≤ T)
    (zeroColor rightColor :
      ActiveHall.Symboling.NonzeroZeroSwapMove X T → C) :
    List (ActiveHall.Symboling.NonzeroZeroSwapMove X T) →
      C → Fin T → ZMod m
  | [], _, _ => 0
  | move :: moves, c, σ =>
      ActiveHall.Symboling.localTradeDelta (m := m)
        (zeroColor move) (rightColor move) c
        ⟨0, Nat.lt_of_lt_of_le (by omega : 0 < 2) hT⟩
        move.right σ +
      nonzeroZeroTradeDeltaSumOfTwoLe hT zeroColor rightColor moves c σ

theorem swapDeltaSum_eq_tradeDeltaSum_of_baseline
    {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : ActiveHall.Incidence T X C} (Φ : ActiveHall.Symboling I)
    (hT : 2 ≤ T)
    (zeroColor rightColor :
      ActiveHall.Symboling.NonzeroZeroSwapMove X T → C) :
    ∀ moves : List (ActiveHall.Symboling.NonzeroZeroSwapMove X T),
      (∀ move, move ∈ moves →
        Φ.color move.vertex
            ⟨0, Nat.lt_of_lt_of_le (by omega : 0 < 2) hT⟩ =
          zeroColor move) →
      (∀ move, move ∈ moves →
        Φ.color move.vertex move.right = rightColor move) →
      Φ.swapDeltaSum (m := m) (nonzeroZeroSwapMovesOfTwoLe hT moves) =
        nonzeroZeroTradeDeltaSumOfTwoLe (m := m) hT zeroColor rightColor
          moves
  | [], _hZero, _hRight => by
      funext c σ
      simp [nonzeroZeroSwapMovesOfTwoLe, nonzeroZeroTradeDeltaSumOfTwoLe,
        ActiveHall.Symboling.nonzeroZeroSwapMoves,
        ActiveHall.Symboling.zeroSwapMoves,
        ActiveHall.Symboling.swapDeltaSum]
  | move :: moves, hZero, hRight => by
      have hTail :=
        swapDeltaSum_eq_tradeDeltaSum_of_baseline (m := m) Φ hT
          zeroColor rightColor moves
          (fun move' hmem => hZero move' (by simp [hmem]))
          (fun move' hmem => hRight move' (by simp [hmem]))
      funext c σ
      have hRightNe :
          (⟨0, Nat.lt_of_lt_of_le (by omega : 0 < 2) hT⟩ : Fin T) ≠
            move.right := by
        intro h
        have hval : move.right.val = 0 := by
          simpa using congrArg Fin.val h.symm
        exact move.right_ne_zero hval
      have hHead :
          Φ.swapMoveDelta (m := m)
              ({ vertex := move.vertex,
                 left := ⟨0, Nat.lt_of_lt_of_le (by omega : 0 < 2) hT⟩,
                 right := move.right } :
                ActiveHall.Symboling.SwapMove X T) c σ =
            ActiveHall.Symboling.localTradeDelta (m := m)
              (zeroColor move) (rightColor move) c
              ⟨0, Nat.lt_of_lt_of_le (by omega : 0 < 2) hT⟩
              move.right σ := by
        simpa [ActiveHall.Symboling.ZeroSwapMove.toSwapMove,
          ActiveHall.Symboling.NonzeroZeroSwapMove.toZeroSwapMove] using
          Φ.swapMoveDelta_eq_localTradeDelta
            (ActiveHall.Symboling.ZeroSwapMove.toSwapMove
              (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT)
              move.toZeroSwapMove)
            hRightNe
            (hZero move (by simp))
            (hRight move (by simp)) c σ
      have hTailPoint := congrFun (congrFun hTail c) σ
      have hTailPoint' :
          Φ.swapDeltaSum (m := m)
              (List.map
                (ActiveHall.Symboling.ZeroSwapMove.toSwapMove
                    (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT) ∘
                  ActiveHall.Symboling.NonzeroZeroSwapMove.toZeroSwapMove)
                moves) c σ =
            nonzeroZeroTradeDeltaSumOfTwoLe (m := m) hT
              zeroColor rightColor moves c σ := by
        simpa [nonzeroZeroSwapMovesOfTwoLe,
          ActiveHall.Symboling.nonzeroZeroSwapMoves,
          ActiveHall.Symboling.zeroSwapMoves] using hTailPoint
      simp [nonzeroZeroSwapMovesOfTwoLe, nonzeroZeroTradeDeltaSumOfTwoLe,
        ActiveHall.Symboling.nonzeroZeroSwapMoves,
        ActiveHall.Symboling.zeroSwapMoves,
        ActiveHall.Symboling.swapDeltaSum,
        ActiveHall.Symboling.NonzeroZeroSwapMove.toZeroSwapMove,
        ActiveHall.Symboling.ZeroSwapMove.toSwapMove, hHead, hTailPoint']

/--
Structured v7.6 reservoir witness for the canonical strict schedule.

The current closure only needs the final equality in
`SuccessorActiveBlockCanonicalNonzeroZeroReservoirSwapScheduleGoal`, but the
paper constructs it through an initial symboling, pairwise distinct `0 ↔ τ`
reservoir toggles, baseline colors at every reserved site, and an arithmetic
delta equation.  This record exposes that intermediate proof surface.
-/
structure CanonicalNonzeroZeroReservoirScript
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (D : ActiveBlockData Cyl) where
  initial : ActiveHall.Symboling Cyl.incidence
  moves :
    List
      (ActiveHall.Symboling.NonzeroZeroSwapMove
        (Shared.TorusVertex (b + 1) m) T)
  swapMoves_pairwise :
    (nonzeroZeroSwapMovesOfTwoLe hT moves).Pairwise
      (fun move₁ move₂ => move₁.vertex ≠ move₂.vertex)
  zeroColor :
    ActiveHall.Symboling.NonzeroZeroSwapMove
      (Shared.TorusVertex (b + 1) m) T →
      Fin (b + T)
  rightColor :
    ActiveHall.Symboling.NonzeroZeroSwapMove
      (Shared.TorusVertex (b + 1) m) T →
      Fin (b + T)
  baseline_zero :
    ∀ move, move ∈ moves →
      initial.color move.vertex
          ⟨0, Nat.lt_of_lt_of_le (by omega : 0 < 2) hT⟩ =
        zeroColor move
  baseline_right :
    ∀ move, move ∈ moves →
      initial.color move.vertex move.right = rightColor move
  target_delta :
    ∀ c σ,
      (activeBlockResidueSpec D).target c σ =
        (initial.residueSpec (m := m)).target c σ +
          nonzeroZeroTradeDeltaSumOfTwoLe (m := m) hT
            zeroColor rightColor moves c σ

namespace CanonicalNonzeroZeroReservoirScript

theorem swapDeltaSum_eq_tradeDeltaSum
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {hT : 2 ≤ T}
    {D : ActiveBlockData Cyl}
    (script : CanonicalNonzeroZeroReservoirScript hT D) :
    script.initial.swapDeltaSum (m := m)
        (nonzeroZeroSwapMovesOfTwoLe hT script.moves) =
      nonzeroZeroTradeDeltaSumOfTwoLe (m := m) hT
        script.zeroColor script.rightColor script.moves :=
  swapDeltaSum_eq_tradeDeltaSum_of_baseline (m := m) script.initial hT
    script.zeroColor script.rightColor script.moves
    script.baseline_zero script.baseline_right

theorem applySwapResidueSpecs_eq
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {hT : 2 ≤ T}
    {D : ActiveBlockData Cyl}
    (script : CanonicalNonzeroZeroReservoirScript hT D) :
    script.initial.applySwapResidueSpecs
        (script.initial.residueSpec (m := m))
        (nonzeroZeroSwapMovesOfTwoLe hT script.moves) =
      activeBlockResidueSpec D := by
  have htarget :
      (script.initial.applySwapResidueSpecs
          (script.initial.residueSpec (m := m))
          (nonzeroZeroSwapMovesOfTwoLe hT script.moves)).target =
        (activeBlockResidueSpec D).target := by
    funext c σ
    rw [ActiveHall.Symboling.applySwapResidueSpecs_target_eq_add_swapDeltaSum_of_pairwise_vertex
      script.initial script.swapMoves_pairwise c σ]
    rw [script.swapDeltaSum_eq_tradeDeltaSum]
    exact (script.target_delta c σ).symm
  cases hleft :
      script.initial.applySwapResidueSpecs
        (script.initial.residueSpec (m := m))
        (nonzeroZeroSwapMovesOfTwoLe hT script.moves) with
  | mk leftTarget =>
      cases hright : activeBlockResidueSpec D with
      | mk rightTarget =>
          have htarget' : leftTarget = rightTarget := by
            rw [hleft, hright] at htarget
            exact htarget
          cases htarget'
          rfl

end CanonicalNonzeroZeroReservoirScript

/--
Successor-scoped script endpoint for the v7.6 canonical reservoir proof.

This is the next constructive target below the strict reservoir schedule: it
asks for the concrete baseline/toggle script whose finite delta is canonical.
-/
def SuccessorActiveBlockCanonicalNonzeroZeroReservoirScriptGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
        ∃ _script : CanonicalNonzeroZeroReservoirScript hT D, True

/--
Successor-scoped local-symbol trade for the canonical active-block schedule.

This is the narrowest v7.3 local-trade surface used by the current closure
adapters.  It asks only for the residue target constructed from
`ActiveBlockData.activeBlock`, not every compatible primitive residue target.
-/
def SuccessorActiveBlockCanonicalLocalSymbolTradeGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
        ActiveHall.SymbolingWithResidues Cyl.incidence
          (activeBlockResidueSpec D)

/--
Paper-facing finite coactive-site reservoir endpoint for the canonical
successor schedule.  This is the Lean name corresponding to the v7.3 reservoir
lemma once it is specialized to the active-block cylinder data consumed
downstream.
-/
def SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal : Prop :=
  SuccessorActiveBlockCanonicalLocalSymbolTradeGoal

/--
Successor-scoped one-site permutation correction for the canonical schedule.

This is a proof surface for the reserved coactive-site construction: it may
first build any residue-realizing symboling `Φ` for a nearby target `R`, but it
must also supply one active vertex and one symbol permutation whose residue
update has exactly the canonical active-block targets.
-/
def SuccessorActiveBlockCanonicalPermutationCorrectionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
        ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
          ∃ Φ : ActiveHall.Symboling Cyl.incidence,
            Φ.HasResidues R ∧
            ∃ x₀ : Shared.TorusVertex (b + 1) m,
              ∃ π : Equiv.Perm (Fin T),
                (∀ c : Fin (b + T),
                  (Φ.permuteResidueSpec R x₀ π).target c
                      ⟨0, by omega⟩ =
                    (D.activeBlock c : ZMod m)) ∧
                (∀ c : Fin (b + T),
                  (Φ.permuteResidueSpec R x₀ π).target c
                      ⟨1, by omega⟩ =
                    -((D.activeBlock c : Nat) : ZMod m)) ∧
                (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
                  (Φ.permuteResidueSpec R x₀ π).target c σ = 0)

/--
Successor-scoped pre-correction form of the one-site reservoir.

This is slightly closer to the expected local-trade proof than
`SuccessorActiveBlockCanonicalPermutationCorrectionGoal`: instead of proving the
three post-permutation canonical target cases directly, it proves that the
realized residue target differs from the canonical target by exactly the local
delta removed and reinserted by a final one-site symbol permutation.
-/
def SuccessorActiveBlockCanonicalPreCorrectionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
        ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
          ∃ Φ : ActiveHall.Symboling Cyl.incidence,
            Φ.HasResidues R ∧
            ∃ x₀ : Shared.TorusVertex (b + 1) m,
              ∃ π : Equiv.Perm (Fin T),
                ∀ c : Fin (b + T), ∀ σ : Fin T,
                  R.target c σ =
                    (activeBlockResidueSpec D).target c σ
                      + (if Φ.color x₀ σ = c then
                          (1 : ZMod m)
                        else 0)
                      - (if Φ.color x₀ (π σ) = c then
                          (1 : ZMod m)
                        else 0)

/--
Broader paper-facing finite coactive-site reservoir endpoint.  This version is
only needed if the reservoir proof naturally handles every compatible primitive
residue schedule, rather than just the canonical active-block schedule.
-/
def SuccessorActiveBlockFiniteCoactiveSiteReservoirGoal : Prop :=
  SuccessorActiveBlockLocalSymbolTradeGoal

/--
Canonical successor feasibility surface.

This is weaker than the canonical local-symbol trade endpoint: it only asks for
a feasible count matrix carrying the canonical active-block residues.  A
separate local-symbol trade theorem can then turn feasibility into a symboling.
-/
def SuccessorActiveBlockCanonicalFeasibleResidueGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
        ActiveHall.FeasibleWithResidues Cyl.incidence
          (activeBlockResidueSpec D)

/--
Canonical successor feasibility reduced to a concrete scaled Hall-slack
witness.

This is the arithmetic residue-rounding surface below
`SuccessorActiveBlockCanonicalFeasibleResidueGoal`: it supplies a count matrix
with the canonical residues plus the scaled proper-cut inequality consumed by
the mixed-expansion slack lemma.
-/
def SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
        ∃ M : ActiveHall.CountMatrix Cyl.incidence,
          M.HasResidues (activeBlockResidueSpec D) ∧
            ∀ U : Finset (Fin (b + T)), ∀ S : Finset (Fin T),
              U.Nonempty → U ≠ Finset.univ →
              S.Nonempty → S ≠ Finset.univ →
                T * M.cutMass U S ≤
                  S.card *
                      (∑ c ∈ U, (Cyl.incidence).colorDegree c) +
                    m * (b + T) * min S.card (T - S.card)

/--
Successor-scoped feasible-to-symboling bridge for the canonical schedule.

This is the corrected local-trade replacement for the unrestricted
`HallRealizationGoal`: it only has to realize the feasible canonical
active-block count matrix on the actual successor cylinder.
-/
def SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      (hT : 2 ≤ T) →
      IsCylinder Cyl →
      (D : ActiveBlockData Cyl) →
      ActiveHall.FeasibleWithResidues Cyl.incidence
        (activeBlockResidueSpec D) →
      ActiveHall.SymbolingWithResidues Cyl.incidence
          (activeBlockResidueSpec D)

/--
Paper-facing feasible coactive-site reservoir endpoint for the canonical
successor schedule.

This is the finite reservoir/local-trade layer after the arithmetic residue
rounding has already supplied `FeasibleWithResidues`.  It is intentionally
definitionally equal to `SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal`,
so downstream endpoints can name the reservoir theorem without reintroducing
the older unrestricted Hall/de Werra surface.
-/
def SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal : Prop :=
  SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal

/--
Combined successor-scoped residue-trade realization endpoint.
-/
def SuccessorActiveBlockResidueTradeRealizationGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      5 ≤ b →
      Odd m → 3 ≤ m → m < b + T →
      packets.length = b →
      (packets.map List.length).sum = b + T →
      (∀ packet, packet ∈ packets → packet.sum = m) →
      (∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
      (∀ packet, packet ∈ packets →
        ∀ q : Nat, 0 < q → q < packet.length →
          Nat.Coprime (packet.take q).sum m) →
      T = b + 1 →
      m ^ b > m * (b + T) * T →
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      (hT : 2 ≤ T) →
        ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
          R.RowCompatible Cyl.incidence ∧
          R.ColCompatible Cyl.incidence ∧
          PrimitiveResidueSpec hT R ∧
          ActiveHall.SymbolingWithResidues Cyl.incidence R

/--
Generic local symbol-trade endpoint.

Once the residue schedule is feasible in the Hall matrix sense, the local
trade layer realizes it by a symboling with those residues.
-/
def LocalSymbolTradeGoal : Prop :=
  ∀ {m T : Nat} {X C : Type} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C],
    ∀ {I : ActiveHall.Incidence T X C}
      {R : ActiveHall.ResidueSpec m T C},
      ActiveHall.FeasibleWithResidues I R →
        ActiveHall.SymbolingWithResidues I R

/--
Cylinder reservoir endpoint for residue schedules.

This is the local-trade reservoir surface: a row/column-compatible primitive
residue specification for the cylinder can be promoted to feasible primitive
residues under the explicitly supplied feasibility bridge.
-/
def CylinderTradeReservoirGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T)
    (R : ActiveHall.ResidueSpec m T (Fin (b + T))),
      R.RowCompatible Cyl.incidence →
      R.ColCompatible Cyl.incidence →
      PrimitiveResidueSpec hT R →
      (R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        PrimitiveResidueSpec hT R →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) →
      HasFeasiblePrimitiveResidues hT Cyl

/--
Active residue-scheduling endpoint.

Given a cylinder and an explicit compatible primitive residue schedule, the
scheduler returns the feasible primitive-residue package expected by the
active-symboling stage.
-/
def ActiveResidueSchedulingGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      IsCylinder Cyl →
      (hT : 2 ≤ T) →
      ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence ∧
        R.ColCompatible Cyl.incidence ∧
        PrimitiveResidueSpec hT R ∧
        ActiveHall.FeasibleWithResidues Cyl.incidence R

/--
Active modular trade-realization endpoint.

This layer consumes the feasible primitive-residue package and realizes a
primitive active symboling for the base-tail cylinder.
-/
def ActiveModularTradeRealizationGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    {hT : 2 ≤ T},
      HasFeasiblePrimitiveResidues hT Cyl →
        ∃ A : ActiveSymboling Cyl, IsPrimitiveActiveSymboling hT A

/-- Direct primitive active-symboling endpoint for the local-trade layer. -/
def PrimitiveActiveSymbolingEndpointGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      IsCylinder Cyl →
      (hT : 2 ≤ T) →
        ∃ A : ActiveSymboling Cyl, IsPrimitiveActiveSymboling hT A

/--
Count-form primitive active-symboling endpoint.

This is the most direct local-trade target for the prefix lift: the trade
construction supplies an active symboling and proves the primitive unit
conditions on the realized symbol counts.
-/
def PrimitiveActiveCountSymbolingEndpointGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      IsCylinder Cyl →
      (hT : 2 ≤ T) →
        ∃ A : ActiveSymboling Cyl,
          IsActiveSymboling A ∧ ActiveSymbolingCountsPrimitive hT A

/--
Active-block local-trade endpoint.

This is the realistic v7.3 small-modulus target: the constructed active-block
cylinder carries enough reservoir structure for local trades to produce a
primitive active symboling.
-/
def ActiveBlockTradeRealizationGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      (hT : 2 ≤ T) →
        ∃ A : ActiveSymboling Cyl, IsPrimitiveActiveSymboling hT A

/--
Count-form active-block local-trade endpoint.  This is the form that feeds the
prefix lift without first restating primitiveity through residue targets.
-/
def ActiveBlockCountTradeRealizationGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets},
      IsCylinder Cyl →
      ActiveBlockData Cyl →
      (hT : 2 ≤ T) →
        ∃ A : ActiveSymboling Cyl,
          IsActiveSymboling A ∧ ActiveSymbolingCountsPrimitive hT A

theorem primitiveResidueSpec_mk {b m T : Nat}
    {hT : 2 ≤ T}
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    (hZero : ∀ c : Fin (b + T),
      IsUnit (R.target c ⟨0, by omega⟩))
    (hNumeric : ∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) :
    PrimitiveResidueSpec hT R := by
  exact ⟨hZero, hNumeric⟩

theorem primitiveResidueSpec_zero {b m T : Nat}
    {hT : 2 ≤ T}
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    (hPrim : PrimitiveResidueSpec hT R) :
    ∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩) :=
  hPrim.1

theorem primitiveResidueSpec_numeric {b m T : Nat}
    {hT : 2 ≤ T}
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    (hPrim : PrimitiveResidueSpec hT R) :
    ∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit (R.target c σ - R.target c ⟨1, by omega⟩) :=
  hPrim.2

theorem activeBlockResidueSpec_compatible_primitive {b m T : Nat}
    [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (D : ActiveBlockData Cyl) (hT : 2 ≤ T) :
    (activeBlockResidueSpec D).RowCompatible Cyl.incidence ∧
      (activeBlockResidueSpec D).ColCompatible Cyl.incidence ∧
      PrimitiveResidueSpec hT (activeBlockResidueSpec D) := by
  classical
  let u : Fin (b + T) → ZMod m := fun c => (D.activeBlock c : ZMod m)
  have huUnit : ∀ c : Fin (b + T), IsUnit (u c) := by
    intro c
    exact D.activeBlock_isUnit c
  have huSum : (∑ c : Fin (b + T), u c) = 0 := by
    change (∑ c : Fin (b + T), ((D.activeBlock c : Nat) : ZMod m)) = 0
    rw [← Nat.cast_sum, D.sum_activeBlock_eq, Nat.cast_mul,
      ZMod.natCast_self, mul_zero]
  have hX :
      (Fintype.card (Shared.TorusVertex (b + 1) m) : ZMod m) = 0 := by
    rw [Shared.card_torusVertex]
    exact ActiveHall.zmod_natCast_pow_eq_zero_of_pos (Nat.succ_pos b)
  refine ⟨?_, ?_, ?_⟩
  · exact
      ActiveHall.universalUnitResidueSpecOfTwoLe_rowCompatible
        hT Cyl.incidence u hCyl.active_degree_mod
  · exact
      ActiveHall.universalUnitResidueSpecOfTwoLe_colCompatible
        hT Cyl.incidence huSum hX
  · exact
      ⟨ActiveHall.universalUnitResidueSpecOfTwoLe_zero_isUnit hT huUnit,
        fun c σ hσ =>
          ActiveHall.universalUnitResidueSpecOfTwoLe_numeric_sub_delta_isUnit
            hT huUnit c hσ⟩

theorem exists_activeBlockResidueSpec_compatible_primitive {b m T : Nat}
    [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (D : ActiveBlockData Cyl) (hT : 2 ≤ T) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧
      R.ColCompatible Cyl.incidence ∧
      PrimitiveResidueSpec hT R := by
  exact ⟨activeBlockResidueSpec D,
    activeBlockResidueSpec_compatible_primitive hCyl D hT⟩

theorem activeBlockResidueScheduleGoal : ActiveBlockResidueScheduleGoal := by
  intro b m T _inst packets Cyl hCyl hBlock hT
  exact exists_activeBlockResidueSpec_compatible_primitive hCyl hBlock hT

theorem successorActiveBlockResidueScheduleGoal :
    SuccessorActiveBlockResidueScheduleGoal := by
  intro b m T _inst packets Cyl _hb5 _hmodd _hm3 _hsmall _hlen _htotal
    _hpacketSum _hpacketUnits _hPrefix _hT_eq _hSlack hCyl hBlock hT
  exact activeBlockResidueScheduleGoal hCyl hBlock hT

theorem successorActiveBlockLocalSymbolTradeGoal_of_compatibleResidueScheduling
    (hSchedule : SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    SuccessorActiveBlockLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock hRow
    hCol _hPrim
  exact hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
    hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock hRow hCol

theorem successorActiveBlockReservoirSwapScheduleGoal_of_initialReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockInitialReservoirSwapScheduleGoal) :
    SuccessorActiveBlockReservoirSwapScheduleGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock
    hRow hCol
  rcases hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock hRow hCol with
    ⟨Φ, moves, hMoves⟩
  exact ⟨Φ.residueSpec (m := m), Φ, Φ.hasResidues_residueSpec,
    moves, hMoves⟩

theorem successorActiveBlockCompatibleResidueSchedulingGoal_of_reservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCompatibleResidueSchedulingGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock
    hRow hCol
  rcases hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock hRow hCol with
    ⟨R₀, Φ, hΦ, moves, hMoves⟩
  exact ⟨Φ.applySwapMoves moves, by
    have hResidues := Φ.applySwapMoves_hasResidues hΦ moves
    simpa [hMoves] using hResidues⟩

theorem successorActiveBlockCompatibleResidueSchedulingGoal_of_initialReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockInitialReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCompatibleResidueSchedulingGoal :=
  successorActiveBlockCompatibleResidueSchedulingGoal_of_reservoirSwapSchedule
    (successorActiveBlockReservoirSwapScheduleGoal_of_initialReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockInitialReservoirSwapScheduleGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockInitialReservoirSwapScheduleGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock
    hRow hCol
  rcases hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock hRow hCol with
    ⟨Φ, moves, hMoves⟩
  exact ⟨Φ,
    ActiveHall.Symboling.zeroSwapMoves
      (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT) moves,
    hMoves⟩

theorem successorActiveBlockZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockZeroReservoirSwapScheduleGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock
    hRow hCol
  rcases hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock hRow hCol with
    ⟨Φ, moves, hMoves⟩
  exact ⟨Φ, moves.map ActiveHall.Symboling.NonzeroZeroSwapMove.toZeroSwapMove,
    hMoves⟩

theorem successorActiveBlockCompatibleResidueSchedulingGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCompatibleResidueSchedulingGoal :=
  successorActiveBlockCompatibleResidueSchedulingGoal_of_initialReservoirSwapSchedule
    (successorActiveBlockInitialReservoirSwapScheduleGoal_of_zeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockInitialReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockInitialReservoirSwapScheduleGoal :=
  successorActiveBlockInitialReservoirSwapScheduleGoal_of_zeroReservoirSwapSchedule
    (successorActiveBlockZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCompatibleResidueSchedulingGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCompatibleResidueSchedulingGoal :=
  successorActiveBlockCompatibleResidueSchedulingGoal_of_zeroReservoirSwapSchedule
    (successorActiveBlockZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockReservoirSwapScheduleGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockReservoirSwapScheduleGoal :=
  successorActiveBlockReservoirSwapScheduleGoal_of_initialReservoirSwapSchedule
    (successorActiveBlockInitialReservoirSwapScheduleGoal_of_zeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockReservoirSwapScheduleGoal :=
  successorActiveBlockReservoirSwapScheduleGoal_of_zeroReservoirSwapSchedule
    (successorActiveBlockZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockLocalSymbolTradeGoal_of_reservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockReservoirSwapScheduleGoal) :
    SuccessorActiveBlockLocalSymbolTradeGoal :=
  successorActiveBlockLocalSymbolTradeGoal_of_compatibleResidueScheduling
    (successorActiveBlockCompatibleResidueSchedulingGoal_of_reservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockLocalSymbolTradeGoal :=
  successorActiveBlockLocalSymbolTradeGoal_of_compatibleResidueScheduling
    (successorActiveBlockCompatibleResidueSchedulingGoal_of_zeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockLocalSymbolTradeGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockLocalSymbolTradeGoal :=
  successorActiveBlockLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    (successorActiveBlockZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_compatibleResidueScheduling
    (hSchedule : SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases activeBlockResidueSpec_compatible_primitive hCyl hBlock hT with
    ⟨hRow, hCol, _hPrim⟩
  exact hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
    hpacketUnits hPrefix hT_eq hSlack hT (activeBlockResidueSpec hBlock)
    hCyl hBlock hRow hCol

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_reservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_compatibleResidueScheduling
    (successorActiveBlockCompatibleResidueSchedulingGoal_of_reservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_compatibleResidueScheduling
    (successorActiveBlockCompatibleResidueSchedulingGoal_of_zeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    (successorActiveBlockZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCanonicalNonzeroZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalNonzeroZeroReservoirSwapScheduleGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases activeBlockResidueSpec_compatible_primitive hCyl hBlock hT with
    ⟨hRow, hCol, _hPrim⟩
  exact hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
    hpacketUnits hPrefix hT_eq hSlack hT (activeBlockResidueSpec hBlock)
    hCyl hBlock hRow hCol

theorem successorActiveBlockCanonicalNonzeroZeroReservoirSwapScheduleGoal_of_script
    (hScript :
      SuccessorActiveBlockCanonicalNonzeroZeroReservoirScriptGoal) :
    SuccessorActiveBlockCanonicalNonzeroZeroReservoirSwapScheduleGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases hScript hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock with
    ⟨script, _hScript⟩
  exact ⟨script.initial, script.moves, by
    simpa [nonzeroZeroSwapMovesOfTwoLe] using
      script.applySwapResidueSpecs_eq⟩

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_canonicalNonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockCanonicalNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock with
    ⟨Φ, moves, hMoves⟩
  let swaps :=
    ActiveHall.Symboling.nonzeroZeroSwapMoves
      (Nat.lt_of_lt_of_le (by omega : 0 < 2) hT) moves
  exact ⟨Φ.applySwapMoves swaps, by
    have hResidues :=
      Φ.applySwapMoves_hasResidues (Φ.hasResidues_residueSpec (m := m)) swaps
    simpa [swaps, hMoves] using hResidues⟩

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_successorLocalTrade
    (hTrade : SuccessorActiveBlockLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases activeBlockResidueSpec_compatible_primitive hCyl hBlock hT with
    ⟨hRow, hCol, hPrim⟩
  exact hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
    hpacketUnits hPrefix hT_eq hSlack hT (activeBlockResidueSpec hBlock)
    hCyl hBlock hRow hCol hPrim

theorem successorActiveBlockLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
    (hReservoir : SuccessorActiveBlockFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockLocalSymbolTradeGoal :=
  hReservoir

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
    (hReservoir : SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  hReservoir

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_permutationCorrection
    (hCorrection : SuccessorActiveBlockCanonicalPermutationCorrectionGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases hCorrection hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock with
    ⟨R, Φ, hΦ, x₀, π, hZero, hOne, hTail⟩
  exact
    symbolingWithResidues_activeBlockResidueSpec_of_permuteResidueSpec_target_cases
      hBlock hT hΦ x₀ π hZero hOne hTail

theorem successorActiveBlockCanonicalPermutationCorrectionGoal_of_preCorrection
    (hPreCorrection : SuccessorActiveBlockCanonicalPreCorrectionGoal) :
    SuccessorActiveBlockCanonicalPermutationCorrectionGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases hPreCorrection hb5 hmodd hm3 hsmall hlen htotal
      hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock with
    ⟨R, Φ, hΦ, x₀, π, hPre⟩
  have hTarget :
      ∀ c σ,
        (Φ.permuteResidueSpec R x₀ π).target c σ =
          (activeBlockResidueSpec hBlock).target c σ :=
    permuteResidueSpec_target_eq_activeBlockResidueSpec_of_preTarget
      hBlock x₀ π hPre
  exact ⟨R, Φ, hΦ, x₀, π,
    (by
      intro c
      rw [hTarget c ⟨0, by omega⟩]
      exact activeBlockResidueSpec_target_zero hBlock c (by omega)),
    (by
      intro c
      rw [hTarget c ⟨1, by omega⟩]
      exact activeBlockResidueSpec_target_one hBlock c (by omega)),
    (by
      intro c σ hσ
      rw [hTarget c σ]
      exact activeBlockResidueSpec_target_of_two_le hBlock c hσ)⟩

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_preCorrection
    (hPreCorrection : SuccessorActiveBlockCanonicalPreCorrectionGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_permutationCorrection
    (successorActiveBlockCanonicalPermutationCorrectionGoal_of_preCorrection
      hPreCorrection)

theorem successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalPreCorrectionGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock with
    ⟨Φ, hΦ⟩
  exact
    ⟨activeBlockResidueSpec hBlock, Φ, hΦ,
      (0 : Shared.TorusVertex (b + 1) m), Equiv.refl (Fin T), by
        intro c σ
        simp only [Equiv.refl_apply]
        by_cases hcolor :
            Φ.color (0 : Shared.TorusVertex (b + 1) m) σ = c
        · simp [hcolor]
        · simp [hcolor]⟩

theorem successorActiveBlockCanonicalPreCorrectionGoal_iff_canonicalLocalTrade :
    SuccessorActiveBlockCanonicalPreCorrectionGoal ↔
      SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  ⟨successorActiveBlockCanonicalLocalSymbolTradeGoal_of_preCorrection,
    successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade⟩

theorem successorActiveBlockCanonicalPreCorrectionGoal_of_finiteCoactiveSiteReservoir
    (hReservoir : SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockCanonicalPreCorrectionGoal :=
  successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
    (successorActiveBlockCanonicalLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
      hReservoir)

theorem successorActiveBlockCanonicalPermutationCorrectionGoal_of_canonicalLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalPermutationCorrectionGoal :=
  successorActiveBlockCanonicalPermutationCorrectionGoal_of_preCorrection
    (successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
      hTrade)

theorem successorActiveBlockCanonicalPermutationCorrectionGoal_iff_canonicalLocalTrade :
    SuccessorActiveBlockCanonicalPermutationCorrectionGoal ↔
      SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  ⟨successorActiveBlockCanonicalLocalSymbolTradeGoal_of_permutationCorrection,
    successorActiveBlockCanonicalPermutationCorrectionGoal_of_canonicalLocalTrade⟩

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_permutationCorrection
    (hCorrection : SuccessorActiveBlockCanonicalPermutationCorrectionGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_permutationCorrection
    hCorrection

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_preCorrection
    (hPreCorrection : SuccessorActiveBlockCanonicalPreCorrectionGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_preCorrection
    hPreCorrection

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_finiteCoactiveSiteReservoir
    (hReservoir : SuccessorActiveBlockFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_successorLocalTrade
    (successorActiveBlockLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
      hReservoir)

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_compatibleResidueScheduling
    (hSchedule : SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_compatibleResidueScheduling
    hSchedule

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_reservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_reservoirSwapSchedule
    hSchedule

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    hSchedule

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_nonzeroZeroReservoirSwapSchedule
    hSchedule

theorem successorActiveBlockCanonicalPreCorrectionGoal_iff_finiteCoactiveSiteReservoir :
    SuccessorActiveBlockCanonicalPreCorrectionGoal ↔
      SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  ⟨successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_preCorrection,
    successorActiveBlockCanonicalPreCorrectionGoal_of_finiteCoactiveSiteReservoir⟩

theorem successorActiveBlockCanonicalFeasibleResidueGoal_of_canonicalLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFeasibleResidueGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  exact
    ActiveHall.feasibleWithResidues_of_symbolingWithResidues
      (hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
        hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock)

theorem successorActiveBlockCanonicalFeasibleResidueGoal_of_scaledFeasibleResidue
    (hScaled : SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal) :
    SuccessorActiveBlockCanonicalFeasibleResidueGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  rcases hScaled hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock with
    ⟨M, hResidues, hScaledCuts⟩
  have hTpos : 0 < T := by omega
  exact
    (hBlock.mixedExpansionData_of_successor hT_eq).feasibleWithResidues_of_scaled_error_le_slack
      hTpos hSlack M hResidues hScaledCuts

theorem successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_canonicalLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
    _hFeasible
  exact hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
    hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock

theorem successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_compatibleResidueScheduling
    (hSchedule : SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_canonicalLocalTrade
    (successorActiveBlockCanonicalLocalSymbolTradeGoal_of_compatibleResidueScheduling
      hSchedule)

theorem successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_reservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_canonicalLocalTrade
    (successorActiveBlockCanonicalLocalSymbolTradeGoal_of_reservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_canonicalLocalTrade
    (successorActiveBlockCanonicalLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    (successorActiveBlockZeroReservoirSwapScheduleGoal_of_nonzeroZeroReservoirSwapSchedule
      hSchedule)

theorem successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_feasibleFiniteCoactiveSiteReservoir
    (hReservoir :
      SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  hReservoir

theorem successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_of_feasibleLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  hTrade

theorem successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_of_canonicalLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_canonicalLocalTrade
    hTrade

theorem successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_of_compatibleResidueScheduling
    (hSchedule : SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_compatibleResidueScheduling
    hSchedule

theorem successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_of_reservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_reservoirSwapSchedule
    hSchedule

theorem successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_of_zeroReservoirSwapSchedule
    (hSchedule : SuccessorActiveBlockZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_zeroReservoirSwapSchedule
    hSchedule

theorem successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_of_nonzeroZeroReservoirSwapSchedule
    (hSchedule :
      SuccessorActiveBlockNonzeroZeroReservoirSwapScheduleGoal) :
    SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_nonzeroZeroReservoirSwapSchedule
    hSchedule

theorem successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_iff_feasibleLocalTrade :
    SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal ↔
      SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  Iff.rfl

theorem activeBlockResidueTradeRealizationGoal_of_schedule_and_localTrade
    (hSchedule : ActiveBlockResidueScheduleGoal)
    (hTrade : ActiveBlockLocalSymbolTradeGoal) :
    ActiveBlockResidueTradeRealizationGoal := by
  intro b m T _instM packets Cyl hCyl hBlock hT
  rcases hSchedule hCyl hBlock hT with ⟨R, hRow, hCol, hPrim⟩
  rcases hTrade hT R hCyl hBlock hRow hCol hPrim with ⟨Φ, hΦ⟩
  exact ⟨R, hRow, hCol, hPrim, Φ, hΦ⟩

theorem successorActiveBlockResidueTradeRealizationGoal_of_schedule_and_localTrade
    (hSchedule : SuccessorActiveBlockResidueScheduleGoal)
    (hTrade : SuccessorActiveBlockLocalSymbolTradeGoal) :
    SuccessorActiveBlockResidueTradeRealizationGoal := by
  intro b m T _instM packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hCyl hBlock hT
  rcases hSchedule hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hCyl hBlock hT with
    ⟨R, hRow, hCol, hPrim⟩
  rcases hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT R hCyl hBlock hRow hCol
      hPrim with
    ⟨Φ, hΦ⟩
  exact ⟨R, hRow, hCol, hPrim, Φ, hΦ⟩

theorem successorActiveBlockResidueTradeRealizationGoal_of_canonicalLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    SuccessorActiveBlockResidueTradeRealizationGoal := by
  intro b m T _instM packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hCyl hBlock hT
  rcases activeBlockResidueSpec_compatible_primitive hCyl hBlock hT with
    ⟨hRow, hCol, hPrim⟩
  rcases hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock with
    ⟨Φ, hΦ⟩
  exact ⟨activeBlockResidueSpec hBlock, hRow, hCol, hPrim, Φ, hΦ⟩

theorem activeBlockTradeRealizationGoal_of_residueTrade
    (hResidueTrade : ActiveBlockResidueTradeRealizationGoal) :
    ActiveBlockTradeRealizationGoal := by
  intro b m T _instM packets Cyl hCyl hBlock hT
  rcases hResidueTrade hCyl hBlock hT with
    ⟨R, _hRow, _hCol, hPrim, Φ, hΦ⟩
  exact ⟨{ R := R, Φ := Φ }, ⟨⟨hΦ⟩, hPrim.1, hPrim.2⟩⟩

theorem activeBlockCountTradeRealizationGoal_of_residueTrade
    (hResidueTrade : ActiveBlockResidueTradeRealizationGoal) :
    ActiveBlockCountTradeRealizationGoal := by
  intro b m T _instM packets Cyl hCyl hBlock hT
  rcases hResidueTrade hCyl hBlock hT with
    ⟨R, _hRow, _hCol, hPrim, Φ, hΦ⟩
  let A : ActiveSymboling Cyl := { R := R, Φ := Φ }
  have hPrimitive : IsPrimitiveActiveSymboling hT A :=
    ⟨⟨hΦ⟩, hPrim.1, hPrim.2⟩
  exact
    ⟨A, hPrimitive.1,
      activeSymbolingCountsPrimitive_of_isPrimitive hT hPrimitive⟩

theorem activeBlockTradeRealizationGoal_of_schedule_and_localTrade
    (hSchedule : ActiveBlockResidueScheduleGoal)
    (hTrade : ActiveBlockLocalSymbolTradeGoal) :
    ActiveBlockTradeRealizationGoal :=
  activeBlockTradeRealizationGoal_of_residueTrade
    (activeBlockResidueTradeRealizationGoal_of_schedule_and_localTrade
      hSchedule hTrade)

theorem primitiveActiveSymbolingEndpointGoal_of_countEndpoint
    (hCount : PrimitiveActiveCountSymbolingEndpointGoal) :
    PrimitiveActiveSymbolingEndpointGoal := by
  intro b m T _instM packets Cyl hCyl hT
  rcases hCount hCyl hT with ⟨A, hA, hPrim⟩
  exact ⟨A, isPrimitiveActiveSymboling_of_countsPrimitive hT hA hPrim⟩

theorem primitiveActiveCountSymbolingEndpointGoal_of_primitiveEndpoint
    (hEndpoint : PrimitiveActiveSymbolingEndpointGoal) :
    PrimitiveActiveCountSymbolingEndpointGoal := by
  intro b m T _instM packets Cyl hCyl hT
  rcases hEndpoint hCyl hT with ⟨A, hA⟩
  exact ⟨A, hA.1, activeSymbolingCountsPrimitive_of_isPrimitive hT hA⟩

theorem activeBlockTradeRealizationGoal_of_count
    (hCount : ActiveBlockCountTradeRealizationGoal) :
    ActiveBlockTradeRealizationGoal := by
  intro b m T _instM packets Cyl hCyl hBlock hT
  rcases hCount hCyl hBlock hT with ⟨A, hA, hPrim⟩
  exact ⟨A, isPrimitiveActiveSymboling_of_countsPrimitive hT hA hPrim⟩

theorem activeBlockCountTradeRealizationGoal_of_trade
    (hTrade : ActiveBlockTradeRealizationGoal) :
    ActiveBlockCountTradeRealizationGoal := by
  intro b m T _instM packets Cyl hCyl hBlock hT
  rcases hTrade hCyl hBlock hT with ⟨A, hA⟩
  exact ⟨A, hA.1, activeSymbolingCountsPrimitive_of_isPrimitive hT hA⟩

theorem activeBlockTradeRealizationGoal_of_globalEndpoint
    (hEndpoint : PrimitiveActiveSymbolingEndpointGoal) :
    ActiveBlockTradeRealizationGoal := by
  intro b m T _instM packets Cyl hCyl _hBlock hT
  exact hEndpoint hCyl hT

theorem activeBlockCountTradeRealizationGoal_of_globalCountEndpoint
    (hEndpoint : PrimitiveActiveCountSymbolingEndpointGoal) :
    ActiveBlockCountTradeRealizationGoal := by
  intro b m T _instM packets Cyl hCyl _hBlock hT
  exact hEndpoint hCyl hT

theorem localSymbolTradeGoal_of_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    LocalSymbolTradeGoal := by
  intro m T X C _instX _instC _decX _decC I R hFeasible
  exact ActiveHall.symbolingWithResidues_of_feasible_and_realization
    hHall hFeasible

theorem successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_localTrade
    (hTrade : LocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl _hb5 _hmodd _hm3 _hsmall _hlen _htotal
    _hpacketSum _hpacketUnits _hPrefix _hT_eq _hSlack _hT _hCyl _hBlock
    hFeasible
  exact hTrade hFeasible

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_localTrade
    (hFeasible : SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hTrade : LocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  exact hTrade
    (hFeasible hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock)

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
    (hFeasible : SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hTrade : SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  exact hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
    hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
    (hFeasible hb5 hmodd hm3 hsmall hlen htotal hpacketSum
      hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock)

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleFiniteCoactiveSiteReservoir
    (hFeasible : SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hReservoir :
      SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
    hFeasible
    (successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_feasibleFiniteCoactiveSiteReservoir
      hReservoir)

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_iff_feasible_and_feasibleLocalTrade :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal ↔
      SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
        SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  ⟨fun hTrade =>
      ⟨successorActiveBlockCanonicalFeasibleResidueGoal_of_canonicalLocalTrade
          hTrade,
        successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_canonicalLocalTrade
          hTrade⟩,
    fun h =>
      successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
        h.1 h.2⟩

theorem successorActiveBlockCanonicalLocalSymbolTradeGoal_iff_feasible_and_feasibleFiniteCoactiveSiteReservoir :
    SuccessorActiveBlockCanonicalLocalSymbolTradeGoal ↔
      SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
        SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_iff_feasible_and_feasibleLocalTrade.trans
    (Iff.and Iff.rfl
      successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_iff_feasibleLocalTrade.symm)

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_feasible_and_feasibleLocalTrade
    (hFeasible : SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hTrade : SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
    hFeasible hTrade

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_feasible_and_feasibleFiniteCoactiveSiteReservoir
    (hFeasible : SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hReservoir :
      SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleFiniteCoactiveSiteReservoir
    hFeasible hReservoir

theorem successorActiveBlockCanonicalPreCorrectionGoal_iff_feasible_and_feasibleLocalTrade :
    SuccessorActiveBlockCanonicalPreCorrectionGoal ↔
      SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
        SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalPreCorrectionGoal_iff_canonicalLocalTrade.trans
    successorActiveBlockCanonicalLocalSymbolTradeGoal_iff_feasible_and_feasibleLocalTrade

theorem successorActiveBlockCanonicalPreCorrectionGoal_iff_feasible_and_feasibleFiniteCoactiveSiteReservoir :
    SuccessorActiveBlockCanonicalPreCorrectionGoal ↔
      SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
        SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalPreCorrectionGoal_iff_canonicalLocalTrade.trans
    successorActiveBlockCanonicalLocalSymbolTradeGoal_iff_feasible_and_feasibleFiniteCoactiveSiteReservoir

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_iff_feasible_and_feasibleLocalTrade :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal ↔
      SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
        SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal :=
  successorActiveBlockCanonicalPreCorrectionGoal_iff_finiteCoactiveSiteReservoir.symm.trans
    successorActiveBlockCanonicalPreCorrectionGoal_iff_feasible_and_feasibleLocalTrade

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_iff_feasible_and_feasibleFiniteCoactiveSiteReservoir :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal ↔
      SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
        SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalPreCorrectionGoal_iff_finiteCoactiveSiteReservoir.symm.trans
    successorActiveBlockCanonicalPreCorrectionGoal_iff_feasible_and_feasibleFiniteCoactiveSiteReservoir

theorem cylinderTradeReservoirGoal :
    CylinderTradeReservoirGoal := by
  intro b m T _instM packets Cyl hT R hRow hCol hPrim hFeasible
  exact ⟨R, hFeasible hRow hCol hPrim, hPrim.1, hPrim.2⟩

theorem activeResidueSchedulingGoal_of_feasiblePrimitiveResidues
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    {hT : 2 ≤ T}
    (hResidues : HasFeasiblePrimitiveResidues hT Cyl) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧
      R.ColCompatible Cyl.incidence ∧
      PrimitiveResidueSpec hT R ∧
      ActiveHall.FeasibleWithResidues Cyl.incidence R := by
  rcases hResidues with ⟨R, hFeasible, hZero, hNumeric⟩
  exact ⟨R, hFeasible.rowCompatible, hFeasible.colCompatible,
    ⟨hZero, hNumeric⟩, hFeasible⟩

theorem feasiblePrimitiveResidues_of_activeResidueSchedule
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    {hT : 2 ≤ T}
    (hSchedule :
      ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence ∧
        R.ColCompatible Cyl.incidence ∧
        PrimitiveResidueSpec hT R ∧
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    HasFeasiblePrimitiveResidues hT Cyl := by
  rcases hSchedule with ⟨R, _hRow, _hCol, hPrim, hFeasible⟩
  exact ⟨R, hFeasible, hPrim.1, hPrim.2⟩

theorem activeModularTradeRealizationGoal_of_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    ActiveModularTradeRealizationGoal := by
  intro b m T _instM packets Cyl hT hResidues
  exact primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
    hHall hResidues

theorem primitiveActiveSymbolingEndpointGoal_of_scheduling_and_realization
    (hSchedule : ActiveResidueSchedulingGoal)
    (hRealize : ActiveModularTradeRealizationGoal) :
    PrimitiveActiveSymbolingEndpointGoal := by
  intro b m T _instM packets Cyl hCyl hT
  rcases hSchedule hCyl hT with
    ⟨R, _hRow, _hCol, hPrim, hFeasible⟩
  exact hRealize ⟨R, hFeasible, hPrim.1, hPrim.2⟩

theorem primitiveActiveSymbolingEndpointGoal_of_residues_and_hallRealization
    (hResidues :
      ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
        {Cyl : Cylinder b m T packets},
          IsCylinder Cyl →
          (hT : 2 ≤ T) →
            HasFeasiblePrimitiveResidues hT Cyl)
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    PrimitiveActiveSymbolingEndpointGoal := by
  intro b m T _instM packets Cyl hCyl hT
  exact
    primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall (hResidues hCyl hT)

theorem activeModularTradeRealizationGoal_of_localSymbolTrade
    (hTrade : LocalSymbolTradeGoal) :
    ActiveModularTradeRealizationGoal := by
  intro b m T _instM packets Cyl hT hResidues
  rcases hResidues with ⟨R, hFeasible, hZero, hNumeric⟩
  rcases hTrade hFeasible with ⟨Φ, hΦ⟩
  exact ⟨{ R := R, Φ := Φ }, ⟨⟨hΦ⟩, hZero, hNumeric⟩⟩

theorem primitiveActiveSymbolingEndpointGoal_of_scheduling_and_localSymbolTrade
    (hSchedule : ActiveResidueSchedulingGoal)
    (hTrade : LocalSymbolTradeGoal) :
    PrimitiveActiveSymbolingEndpointGoal :=
  primitiveActiveSymbolingEndpointGoal_of_scheduling_and_realization
    hSchedule
    (activeModularTradeRealizationGoal_of_localSymbolTrade hTrade)

theorem primitiveActiveCountSymbolingEndpointGoal_of_scheduling_and_localSymbolTrade
    (hSchedule : ActiveResidueSchedulingGoal)
    (hTrade : LocalSymbolTradeGoal) :
    PrimitiveActiveCountSymbolingEndpointGoal :=
  primitiveActiveCountSymbolingEndpointGoal_of_primitiveEndpoint
    (primitiveActiveSymbolingEndpointGoal_of_scheduling_and_localSymbolTrade
      hSchedule hTrade)

end Trades
end BaseTail
end Concrete
end RoundComposite
