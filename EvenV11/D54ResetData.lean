import EvenV11.LowD5M4Seed

namespace EvenV11
namespace D54ResetData

abbrev Y4 := ZMod 4
abbrev Z4 := ZMod 4

structure D54Cylinder where
  q : TerminalQ 4
  y : Y4
  deriving DecidableEq, Repr

inductive D54ReserveRole where
  | U0
  | U1
  | U2
  | U1c
  | U2c
  | U3c
  | U4c
  | Ustar
  deriving DecidableEq, Repr

structure D54ReservePoint where
  role : D54ReserveRole
  q : TerminalQ 4
  y : Y4
  z : Z4
  deriving DecidableEq, Repr

structure D54Point where
  q : TerminalQ 4
  y : Y4
  z : Z4
  deriving DecidableEq, Repr

def d54q4 (x y : Nat) : TerminalQ 4 :=
  TerminalA2LowMod.q4 x y

def d54PointOfReserve (r : D54ReservePoint) : D54Point where
  q := r.q
  y := r.y
  z := r.z

def d54TerminalSelector : List (TerminalQ 4) :=
  [d54q4 0 3, d54q4 3 0, d54q4 3 3]

def d54TerminalResetSites : List (TerminalQ 4) :=
  [d54q4 0 0, d54q4 1 0, d54q4 2 2]

def d54TerminalResetSite : Fin 3 → TerminalQ 4
  | 0 => d54q4 0 0
  | 1 => d54q4 1 0
  | 2 => d54q4 2 2

def d54FinalCylinders : List D54Cylinder :=
  [ { q := d54q4 0 0, y := (0 : Y4) },
    { q := d54q4 0 0, y := (1 : Y4) },
    { q := d54q4 0 0, y := (2 : Y4) },
    { q := d54q4 0 0, y := (3 : Y4) },
    { q := d54q4 0 1, y := (0 : Y4) } ]

def d54FinalCylinderOfColor : Fin 5 → D54Cylinder
  | 0 => { q := d54q4 0 0, y := (0 : Y4) }
  | 1 => { q := d54q4 0 0, y := (1 : Y4) }
  | 2 => { q := d54q4 0 0, y := (2 : Y4) }
  | 3 => { q := d54q4 0 0, y := (3 : Y4) }
  | 4 => { q := d54q4 0 1, y := (0 : Y4) }

def d54LiftedSelector : List D54Point :=
  d54TerminalSelector.map fun q =>
    { q := q, y := (0 : Y4), z := (0 : Z4) }

def d54ReservePoints : List D54ReservePoint :=
  [ { role := D54ReserveRole.U0,
      q := d54q4 0 2, y := (1 : Y4), z := (1 : Z4) },
    { role := D54ReserveRole.U1,
      q := d54q4 1 1, y := (1 : Y4), z := (1 : Z4) },
    { role := D54ReserveRole.U2,
      q := d54q4 2 0, y := (1 : Y4), z := (1 : Z4) },
    { role := D54ReserveRole.U1c,
      q := d54q4 0 2, y := (1 : Y4), z := (2 : Z4) },
    { role := D54ReserveRole.U2c,
      q := d54q4 1 1, y := (1 : Y4), z := (2 : Z4) },
    { role := D54ReserveRole.U3c,
      q := d54q4 2 0, y := (1 : Y4), z := (2 : Z4) },
    { role := D54ReserveRole.U4c,
      q := d54q4 3 2, y := (1 : Y4), z := (2 : Z4) },
    { role := D54ReserveRole.Ustar,
      q := d54q4 0 2, y := (1 : Y4), z := (3 : Z4) } ]

def d54ReserveRoles : List D54ReserveRole :=
  [ D54ReserveRole.U0,
    D54ReserveRole.U1,
    D54ReserveRole.U2,
    D54ReserveRole.U1c,
    D54ReserveRole.U2c,
    D54ReserveRole.U3c,
    D54ReserveRole.U4c,
    D54ReserveRole.Ustar ]

def d54ReservePointOfRole : D54ReserveRole → D54ReservePoint
  | D54ReserveRole.U0 =>
      { role := D54ReserveRole.U0,
        q := d54q4 0 2, y := (1 : Y4), z := (1 : Z4) }
  | D54ReserveRole.U1 =>
      { role := D54ReserveRole.U1,
        q := d54q4 1 1, y := (1 : Y4), z := (1 : Z4) }
  | D54ReserveRole.U2 =>
      { role := D54ReserveRole.U2,
        q := d54q4 2 0, y := (1 : Y4), z := (1 : Z4) }
  | D54ReserveRole.U1c =>
      { role := D54ReserveRole.U1c,
        q := d54q4 0 2, y := (1 : Y4), z := (2 : Z4) }
  | D54ReserveRole.U2c =>
      { role := D54ReserveRole.U2c,
        q := d54q4 1 1, y := (1 : Y4), z := (2 : Z4) }
  | D54ReserveRole.U3c =>
      { role := D54ReserveRole.U3c,
        q := d54q4 2 0, y := (1 : Y4), z := (2 : Z4) }
  | D54ReserveRole.U4c =>
      { role := D54ReserveRole.U4c,
        q := d54q4 3 2, y := (1 : Y4), z := (2 : Z4) }
  | D54ReserveRole.Ustar =>
      { role := D54ReserveRole.Ustar,
        q := d54q4 0 2, y := (1 : Y4), z := (3 : Z4) }

theorem d54ReservePoints_eq_map_reservePointOfRole :
    d54ReservePoints = d54ReserveRoles.map d54ReservePointOfRole := by
  rfl

def d54ReserveD54PointOfRole (role : D54ReserveRole) : D54Point :=
  d54PointOfReserve (d54ReservePointOfRole role)

def neBool {α : Type*} [DecidableEq α] (a b : α) : Bool :=
  decide (a ≠ b)

def listsDisjoint {α : Type*} [DecidableEq α] (xs ys : List α) :
    Prop :=
  xs.all (fun x => ys.all (fun y => neBool x y)) = true

def reservePoints : List D54Point :=
  d54ReservePoints.map d54PointOfReserve

theorem reservePoints_eq_map_reserveD54PointOfRole :
    reservePoints = d54ReserveRoles.map d54ReserveD54PointOfRole := by
  rfl

def cylinderAvoidsPoint (cylinder : D54Cylinder) (point : D54Point) :
    Bool :=
  neBool cylinder.q point.q || neBool cylinder.y point.y

def cylindersAvoidPoints
    (cylinders : List D54Cylinder) (points : List D54Point) :
    Prop :=
  cylinders.all (fun cylinder =>
    points.all (fun point => cylinderAvoidsPoint cylinder point)) = true

def reserveAvoidsCylinder (point : D54Point) (cylinder : D54Cylinder) :
    Bool :=
  neBool point.q cylinder.q || neBool point.y cylinder.y

def reservesAvoidCylinders
    (points : List D54Point) (cylinders : List D54Cylinder) : Prop :=
  points.all (fun point =>
    cylinders.all (fun cylinder => reserveAvoidsCylinder point cylinder)) = true

theorem neBool_eq_true_iff
    {α : Type*} [DecidableEq α] (a b : α) :
    neBool a b = true ↔ a ≠ b := by
  simp [neBool]

theorem listsDisjoint_ne_of_mem
    {α : Type*} [DecidableEq α] {xs ys : List α}
    (h : listsDisjoint xs ys) {x y : α}
    (hx : x ∈ xs) (hy : y ∈ ys) :
    x ≠ y := by
  unfold listsDisjoint at h
  have hxAll := (List.all_eq_true).1 h x hx
  have hyNe := (List.all_eq_true).1 hxAll y hy
  exact (neBool_eq_true_iff x y).1 hyNe

theorem cylinderAvoidsPoint_eq_true_iff
    (cylinder : D54Cylinder) (point : D54Point) :
    cylinderAvoidsPoint cylinder point = true ↔
      cylinder.q ≠ point.q ∨ cylinder.y ≠ point.y := by
  simp [cylinderAvoidsPoint, neBool]

theorem reserveAvoidsCylinder_eq_true_iff
    (point : D54Point) (cylinder : D54Cylinder) :
    reserveAvoidsCylinder point cylinder = true ↔
      point.q ≠ cylinder.q ∨ point.y ≠ cylinder.y := by
  simp [reserveAvoidsCylinder, neBool]

theorem cylindersAvoidPoints_avoid_of_mem
    {cylinders : List D54Cylinder} {points : List D54Point}
    (h : cylindersAvoidPoints cylinders points)
    {cylinder : D54Cylinder} {point : D54Point}
    (hc : cylinder ∈ cylinders) (hp : point ∈ points) :
    cylinderAvoidsPoint cylinder point = true := by
  unfold cylindersAvoidPoints at h
  have hcAll := (List.all_eq_true).1 h cylinder hc
  exact (List.all_eq_true).1 hcAll point hp

theorem cylindersAvoidPoints_ne_or_ne_of_mem
    {cylinders : List D54Cylinder} {points : List D54Point}
    (h : cylindersAvoidPoints cylinders points)
    {cylinder : D54Cylinder} {point : D54Point}
    (hc : cylinder ∈ cylinders) (hp : point ∈ points) :
    cylinder.q ≠ point.q ∨ cylinder.y ≠ point.y :=
  (cylinderAvoidsPoint_eq_true_iff cylinder point).1
    (cylindersAvoidPoints_avoid_of_mem h hc hp)

theorem reservesAvoidCylinders_avoid_of_mem
    {points : List D54Point} {cylinders : List D54Cylinder}
    (h : reservesAvoidCylinders points cylinders)
    {point : D54Point} {cylinder : D54Cylinder}
    (hp : point ∈ points) (hc : cylinder ∈ cylinders) :
    reserveAvoidsCylinder point cylinder = true := by
  unfold reservesAvoidCylinders at h
  have hpAll := (List.all_eq_true).1 h point hp
  exact (List.all_eq_true).1 hpAll cylinder hc

theorem reservesAvoidCylinders_ne_or_ne_of_mem
    {points : List D54Point} {cylinders : List D54Cylinder}
    (h : reservesAvoidCylinders points cylinders)
    {point : D54Point} {cylinder : D54Cylinder}
    (hp : point ∈ points) (hc : cylinder ∈ cylinders) :
    point.q ≠ cylinder.q ∨ point.y ≠ cylinder.y :=
  (reserveAvoidsCylinder_eq_true_iff point cylinder).1
    (reservesAvoidCylinders_avoid_of_mem h hp hc)

theorem d54TerminalSelector_nodup :
    d54TerminalSelector.Nodup := by
  decide

theorem d54TerminalResetSites_nodup :
    d54TerminalResetSites.Nodup := by
  decide

theorem d54TerminalResetSites_disjoint_selector :
    listsDisjoint d54TerminalResetSites d54TerminalSelector := by
  rfl

theorem d54TerminalResetSite_eq_lowD5M4
    (i : Fin 3) :
    d54TerminalResetSite i =
      match i with
      | 0 => LowD5M4.p0
      | 1 => LowD5M4.p1
      | 2 => LowD5M4.p2 := by
  fin_cases i <;> rfl

theorem d54TerminalResetSites_eq_lowD5M4 :
    d54TerminalResetSites =
      [LowD5M4.p0, LowD5M4.p1, LowD5M4.p2] := by
  rfl

theorem d54FinalCylinders_nodup :
    d54FinalCylinders.Nodup := by
  decide

theorem d54FinalCylinders_avoid_liftedSelector :
    cylindersAvoidPoints d54FinalCylinders d54LiftedSelector := by
  rfl

theorem d54FinalCylinderOfColor_eq_lowD5M4_liftSite
    (c : Fin 5) :
    d54FinalCylinderOfColor c =
      { q := (LowD5M4.liftSite c).1,
        y := (LowD5M4.liftSite c).2 } := by
  fin_cases c <;> rfl

theorem d54FinalCylinders_eq_lowD5M4_liftSites :
    d54FinalCylinders =
      [ { q := (LowD5M4.liftSite 0).1,
          y := (LowD5M4.liftSite 0).2 },
        { q := (LowD5M4.liftSite 1).1,
          y := (LowD5M4.liftSite 1).2 },
        { q := (LowD5M4.liftSite 2).1,
          y := (LowD5M4.liftSite 2).2 },
        { q := (LowD5M4.liftSite 3).1,
          y := (LowD5M4.liftSite 3).2 },
        { q := (LowD5M4.liftSite 4).1,
          y := (LowD5M4.liftSite 4).2 } ] := by
  rfl

theorem d54ReservePoints_nodup :
    d54ReservePoints.Nodup := by
  decide

theorem d54ReservePoints_count :
    d54ReservePoints.length = 8 :=
  rfl

theorem d54ReservePoints_avoid_finalCylinders :
    reservesAvoidCylinders reservePoints d54FinalCylinders := by
  rfl

theorem d54ReservePoints_disjoint_liftedSelector :
    listsDisjoint reservePoints d54LiftedSelector := by
  rfl

structure D54ResetTableCertificate where
  terminalOrbitBijective : Function.Bijective terminalResetOrbit4
  terminalStepOrbit :
    ∀ i : Fin 16,
      terminalResetOrbit4Equiv (i + 1) =
        wordEval (terminalSymbolStep 4) terminalResetTrace4
          (terminalResetOrbit4Equiv i)
  terminalSingleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4)
  selectorNodup : d54TerminalSelector.Nodup
  resetSitesNodup : d54TerminalResetSites.Nodup
  resetSitesDisjointSelector :
    listsDisjoint d54TerminalResetSites d54TerminalSelector
  resetSitesEqLowD5M4 :
    d54TerminalResetSites =
      [LowD5M4.p0, LowD5M4.p1, LowD5M4.p2]
  finalCylindersNodup : d54FinalCylinders.Nodup
  finalCylindersAvoidLiftedSelector :
    cylindersAvoidPoints d54FinalCylinders d54LiftedSelector
  finalCylindersEqLowD5M4 :
    d54FinalCylinders =
      [ { q := (LowD5M4.liftSite 0).1,
          y := (LowD5M4.liftSite 0).2 },
        { q := (LowD5M4.liftSite 1).1,
          y := (LowD5M4.liftSite 1).2 },
        { q := (LowD5M4.liftSite 2).1,
          y := (LowD5M4.liftSite 2).2 },
        { q := (LowD5M4.liftSite 3).1,
          y := (LowD5M4.liftSite 3).2 },
        { q := (LowD5M4.liftSite 4).1,
          y := (LowD5M4.liftSite 4).2 } ]
  reservePointsNodup : d54ReservePoints.Nodup
  reservePointsCount : d54ReservePoints.length = 8
  reservePointsAvoidFinalCylinders :
    reservesAvoidCylinders reservePoints d54FinalCylinders
  reservePointsDisjointLiftedSelector :
    listsDisjoint reservePoints d54LiftedSelector

def d54ResetTableCertificate : D54ResetTableCertificate where
  terminalOrbitBijective := terminalResetOrbit4_bijective
  terminalStepOrbit := terminalResetTrace4_stepOrbit
  terminalSingleCycle := terminalResetTrace4_singleCycle
  selectorNodup := d54TerminalSelector_nodup
  resetSitesNodup := d54TerminalResetSites_nodup
  resetSitesDisjointSelector := d54TerminalResetSites_disjoint_selector
  resetSitesEqLowD5M4 := d54TerminalResetSites_eq_lowD5M4
  finalCylindersNodup := d54FinalCylinders_nodup
  finalCylindersAvoidLiftedSelector :=
    d54FinalCylinders_avoid_liftedSelector
  finalCylindersEqLowD5M4 :=
    d54FinalCylinders_eq_lowD5M4_liftSites
  reservePointsNodup := d54ReservePoints_nodup
  reservePointsCount := d54ReservePoints_count
  reservePointsAvoidFinalCylinders :=
    d54ReservePoints_avoid_finalCylinders
  reservePointsDisjointLiftedSelector :=
    d54ReservePoints_disjoint_liftedSelector

theorem d54ResetTableCertificate_terminalOrbitBijective :
    Function.Bijective terminalResetOrbit4 :=
  d54ResetTableCertificate.terminalOrbitBijective

theorem d54ResetTableCertificate_terminalStepOrbit :
    ∀ i : Fin 16,
      terminalResetOrbit4Equiv (i + 1) =
        wordEval (terminalSymbolStep 4) terminalResetTrace4
          (terminalResetOrbit4Equiv i) :=
  d54ResetTableCertificate.terminalStepOrbit

theorem d54ResetTableCertificate_terminalSingleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  d54ResetTableCertificate.terminalSingleCycle

theorem d54ResetTableCertificate_selectorNodup :
    d54TerminalSelector.Nodup :=
  d54ResetTableCertificate.selectorNodup

theorem d54ResetTableCertificate_resetSitesNodup :
    d54TerminalResetSites.Nodup :=
  d54ResetTableCertificate.resetSitesNodup

theorem d54ResetTableCertificate_resetSitesDisjointSelector :
    listsDisjoint d54TerminalResetSites d54TerminalSelector :=
  d54ResetTableCertificate.resetSitesDisjointSelector

theorem d54ResetTableCertificate_resetSitesEqLowD5M4 :
    d54TerminalResetSites =
      [LowD5M4.p0, LowD5M4.p1, LowD5M4.p2] :=
  d54ResetTableCertificate.resetSitesEqLowD5M4

theorem d54ResetTableCertificate_finalCylindersNodup :
    d54FinalCylinders.Nodup :=
  d54ResetTableCertificate.finalCylindersNodup

theorem d54ResetTableCertificate_finalCylindersAvoidLiftedSelector :
    cylindersAvoidPoints d54FinalCylinders d54LiftedSelector :=
  d54ResetTableCertificate.finalCylindersAvoidLiftedSelector

theorem d54ResetTableCertificate_finalCylindersEqLowD5M4 :
    d54FinalCylinders =
      [ { q := (LowD5M4.liftSite 0).1,
          y := (LowD5M4.liftSite 0).2 },
        { q := (LowD5M4.liftSite 1).1,
          y := (LowD5M4.liftSite 1).2 },
        { q := (LowD5M4.liftSite 2).1,
          y := (LowD5M4.liftSite 2).2 },
        { q := (LowD5M4.liftSite 3).1,
          y := (LowD5M4.liftSite 3).2 },
        { q := (LowD5M4.liftSite 4).1,
          y := (LowD5M4.liftSite 4).2 } ] :=
  d54ResetTableCertificate.finalCylindersEqLowD5M4

theorem d54ResetTableCertificate_reservePointsNodup :
    d54ReservePoints.Nodup :=
  d54ResetTableCertificate.reservePointsNodup

theorem d54ResetTableCertificate_reservePointsCount :
    d54ReservePoints.length = 8 :=
  d54ResetTableCertificate.reservePointsCount

theorem d54ResetTableCertificate_reservePointsAvoidFinalCylinders :
    reservesAvoidCylinders reservePoints d54FinalCylinders :=
  d54ResetTableCertificate.reservePointsAvoidFinalCylinders

theorem d54ResetTableCertificate_reservePointsDisjointLiftedSelector :
    listsDisjoint reservePoints d54LiftedSelector :=
  d54ResetTableCertificate.reservePointsDisjointLiftedSelector

end D54ResetData

export D54ResetData
  (Y4 Z4 D54Cylinder D54ReserveRole D54ReservePoint D54Point
   d54TerminalSelector d54TerminalResetSites d54FinalCylinders
   d54TerminalResetSite d54FinalCylinderOfColor
   d54LiftedSelector d54ReservePoints d54ReserveRoles
   d54ReservePointOfRole d54ReserveD54PointOfRole reservePoints
   listsDisjoint cylindersAvoidPoints reservesAvoidCylinders
   neBool_eq_true_iff listsDisjoint_ne_of_mem
   cylinderAvoidsPoint_eq_true_iff reserveAvoidsCylinder_eq_true_iff
   cylindersAvoidPoints_avoid_of_mem
   cylindersAvoidPoints_ne_or_ne_of_mem
   reservesAvoidCylinders_avoid_of_mem
   reservesAvoidCylinders_ne_or_ne_of_mem
   d54ReservePoints_eq_map_reservePointOfRole
   reservePoints_eq_map_reserveD54PointOfRole
   d54TerminalSelector_nodup d54TerminalResetSites_nodup
   d54TerminalResetSites_disjoint_selector
   d54TerminalResetSite_eq_lowD5M4
   d54TerminalResetSites_eq_lowD5M4
   d54FinalCylinders_nodup
   d54FinalCylinders_avoid_liftedSelector d54ReservePoints_nodup
   d54ReservePoints_count d54ReservePoints_avoid_finalCylinders
   d54ReservePoints_disjoint_liftedSelector
   d54FinalCylinderOfColor_eq_lowD5M4_liftSite
   d54FinalCylinders_eq_lowD5M4_liftSites
   D54ResetTableCertificate d54ResetTableCertificate
   d54ResetTableCertificate_terminalOrbitBijective
   d54ResetTableCertificate_terminalStepOrbit
   d54ResetTableCertificate_terminalSingleCycle
   d54ResetTableCertificate_selectorNodup
   d54ResetTableCertificate_resetSitesNodup
   d54ResetTableCertificate_resetSitesDisjointSelector
   d54ResetTableCertificate_resetSitesEqLowD5M4
   d54ResetTableCertificate_finalCylindersNodup
   d54ResetTableCertificate_finalCylindersAvoidLiftedSelector
   d54ResetTableCertificate_finalCylindersEqLowD5M4
   d54ResetTableCertificate_reservePointsNodup
   d54ResetTableCertificate_reservePointsCount
   d54ResetTableCertificate_reservePointsAvoidFinalCylinders
   d54ResetTableCertificate_reservePointsDisjointLiftedSelector)

end EvenV11
