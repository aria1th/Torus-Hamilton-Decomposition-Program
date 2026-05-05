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

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_finiteCoactiveSiteReservoir
    (hReservoir : SuccessorActiveBlockFiniteCoactiveSiteReservoirGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_successorLocalTrade
    (successorActiveBlockLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
      hReservoir)

theorem successorActiveBlockCanonicalFeasibleResidueGoal_of_canonicalLocalTrade
    (hTrade : SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFeasibleResidueGoal := by
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock
  exact
    ActiveHall.feasibleWithResidues_of_symbolingWithResidues
      (hTrade hb5 hmodd hm3 hsmall hlen htotal hpacketSum
        hpacketUnits hPrefix hT_eq hSlack hT hCyl hBlock)

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

theorem successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_feasible_and_feasibleLocalTrade
    (hFeasible : SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hTrade : SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal :=
  successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
    hFeasible hTrade

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
