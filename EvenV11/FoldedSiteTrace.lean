import EvenV11.TerminalA2LowMod

namespace EvenV11
namespace FoldedSiteTrace

inductive FoldedRole where
  | x0
  | x1
  | x2
  | r0
  | r1
  | c1
  | c2
  deriving DecidableEq, Repr

structure FoldedCoord (m : Nat) where
  y : TerminalQ m
  q : TerminalQ m
  z : TerminalQ m
  deriving DecidableEq, Repr

structure TerminalHit where
  slot : Nat
  symbol : TerminalSymbol
  deriving DecidableEq, Repr

structure FoldedSwitchingSite (m : Nat) where
  role : FoldedRole
  coord : FoldedCoord m
  code : Nat
  hit : Option TerminalHit
  deriving DecidableEq, Repr

def foldedCoord {m : Nat}
    (y0 y1 q0 q1 z0 z1 : Nat) : FoldedCoord m where
  y := ((y0 : ZMod m), (y1 : ZMod m))
  q := ((q0 : ZMod m), (q1 : ZMod m))
  z := ((z0 : ZMod m), (z1 : ZMod m))

def foldedCoordCode {m : Nat} [NeZero m] (coord : FoldedCoord m) :
    Nat :=
  coord.y.1.val +
    m * coord.y.2.val +
      m ^ 2 * coord.q.1.val +
        m ^ 3 * coord.q.2.val +
          m ^ 4 * coord.z.1.val +
            m ^ 5 * coord.z.2.val

def codeMatches {m : Nat} [NeZero m] (site : FoldedSwitchingSite m) :
    Bool :=
  site.code == foldedCoordCode site.coord

def allCodesMatch {m : Nat} [NeZero m]
    (sites : List (FoldedSwitchingSite m)) : Prop :=
  sites.all codeMatches = true

def hit (slot : Nat) (symbol : TerminalSymbol) : Option TerminalHit :=
  some { slot, symbol }

def hitSymbolsAt {m : Nat} (slot : Nat)
    (sites : List (FoldedSwitchingSite m)) : List TerminalSymbol :=
  sites.filterMap fun site =>
    match site.hit with
    | some h => if h.slot = slot then some h.symbol else none
    | none => none

def chronologicalTrace {m : Nat} (period : Nat)
    (sites : List (FoldedSwitchingSite m)) : List TerminalSymbol :=
  (List.range period).flatMap fun slot => hitSymbolsAt slot sites

def foldedSiteRoles {m : Nat}
    (sites : List (FoldedSwitchingSite m)) : List FoldedRole :=
  sites.map fun site => site.role

def foldedSiteCodes {m : Nat}
    (sites : List (FoldedSwitchingSite m)) : List Nat :=
  sites.map fun site => site.code

def foldedSiteHits {m : Nat}
    (sites : List (FoldedSwitchingSite m)) : List TerminalHit :=
  sites.filterMap fun site => site.hit

def foldedRoleTable : List FoldedRole :=
  [FoldedRole.x0, FoldedRole.x1, FoldedRole.x2, FoldedRole.r0,
    FoldedRole.r1, FoldedRole.c1, FoldedRole.c2]

def foldedSites4 : List (FoldedSwitchingSite 4) :=
  [ { role := FoldedRole.x0,
      coord := foldedCoord 0 0 0 0 0 0, code := 0,
      hit := hit 1 TerminalSymbol.F0 },
    { role := FoldedRole.x1,
      coord := foldedCoord 0 0 1 0 0 0, code := 16,
      hit := none },
    { role := FoldedRole.x2,
      coord := foldedCoord 0 1 0 1 0 1, code := 1092,
      hit := hit 3 TerminalSymbol.F1 },
    { role := FoldedRole.r0,
      coord := foldedCoord 0 0 0 2 0 0, code := 128,
      hit := hit 2 TerminalSymbol.F0 },
    { role := FoldedRole.r1,
      coord := foldedCoord 0 0 1 2 0 0, code := 144,
      hit := none },
    { role := FoldedRole.c1,
      coord := foldedCoord 0 0 2 0 0 0, code := 32,
      hit := none },
    { role := FoldedRole.c2,
      coord := foldedCoord 0 0 2 1 0 0, code := 96,
      hit := none } ]

def foldedSites6 : List (FoldedSwitchingSite 6) :=
  [ { role := FoldedRole.x0,
      coord := foldedCoord 0 0 0 0 0 0, code := 0,
      hit := hit 1 TerminalSymbol.F0 },
    { role := FoldedRole.x1,
      coord := foldedCoord 0 0 1 0 0 0, code := 36,
      hit := none },
    { role := FoldedRole.x2,
      coord := foldedCoord 0 1 4 4 0 0, code := 1014,
      hit := hit 4 TerminalSymbol.F1 },
    { role := FoldedRole.r0,
      coord := foldedCoord 0 0 3 1 0 0, code := 324,
      hit := hit 2 TerminalSymbol.F0 },
    { role := FoldedRole.r1,
      coord := foldedCoord 0 0 4 5 0 0, code := 1224,
      hit := hit 3 TerminalSymbol.F0 },
    { role := FoldedRole.c1,
      coord := foldedCoord 0 0 4 3 0 0, code := 792,
      hit := hit 5 TerminalSymbol.F1 },
    { role := FoldedRole.c2,
      coord := foldedCoord 0 0 2 1 0 0, code := 288,
      hit := none } ]

theorem foldedSites4_codes :
    allCodesMatch (m := 4) foldedSites4 := by
  rfl

theorem foldedSites6_codes :
    allCodesMatch (m := 6) foldedSites6 := by
  rfl

theorem foldedSites4_length :
    foldedSites4.length = 7 :=
  rfl

theorem foldedSites6_length :
    foldedSites6.length = 7 :=
  rfl

theorem foldedSites4_roles :
    foldedSiteRoles foldedSites4 = foldedRoleTable :=
  rfl

theorem foldedSites6_roles :
    foldedSiteRoles foldedSites6 = foldedRoleTable :=
  rfl

theorem foldedSites4_roles_nodup :
    (foldedSiteRoles foldedSites4).Nodup := by
  decide

theorem foldedSites6_roles_nodup :
    (foldedSiteRoles foldedSites6).Nodup := by
  decide

theorem foldedSites4_codeList :
    foldedSiteCodes foldedSites4 = [0, 16, 1092, 128, 144, 32, 96] :=
  rfl

theorem foldedSites6_codeList :
    foldedSiteCodes foldedSites6 = [0, 36, 1014, 324, 1224, 792, 288] :=
  rfl

theorem foldedSites4_hits :
    foldedSiteHits foldedSites4 =
      [ { slot := 1, symbol := TerminalSymbol.F0 },
        { slot := 3, symbol := TerminalSymbol.F1 },
        { slot := 2, symbol := TerminalSymbol.F0 } ] :=
  rfl

theorem foldedSites6_hits :
    foldedSiteHits foldedSites6 =
      [ { slot := 1, symbol := TerminalSymbol.F0 },
        { slot := 4, symbol := TerminalSymbol.F1 },
        { slot := 2, symbol := TerminalSymbol.F0 },
        { slot := 3, symbol := TerminalSymbol.F0 },
        { slot := 5, symbol := TerminalSymbol.F1 } ] :=
  rfl

theorem foldedSites4_hitSymbolsAt_zero :
    hitSymbolsAt 0 foldedSites4 = [] :=
  rfl

theorem foldedSites4_hitSymbolsAt_one :
    hitSymbolsAt 1 foldedSites4 = [TerminalSymbol.F0] :=
  rfl

theorem foldedSites4_hitSymbolsAt_two :
    hitSymbolsAt 2 foldedSites4 = [TerminalSymbol.F0] :=
  rfl

theorem foldedSites4_hitSymbolsAt_three :
    hitSymbolsAt 3 foldedSites4 = [TerminalSymbol.F1] :=
  rfl

theorem foldedSites6_hitSymbolsAt_zero :
    hitSymbolsAt 0 foldedSites6 = [] :=
  rfl

theorem foldedSites6_hitSymbolsAt_one :
    hitSymbolsAt 1 foldedSites6 = [TerminalSymbol.F0] :=
  rfl

theorem foldedSites6_hitSymbolsAt_two :
    hitSymbolsAt 2 foldedSites6 = [TerminalSymbol.F0] :=
  rfl

theorem foldedSites6_hitSymbolsAt_three :
    hitSymbolsAt 3 foldedSites6 = [TerminalSymbol.F0] :=
  rfl

theorem foldedSites6_hitSymbolsAt_four :
    hitSymbolsAt 4 foldedSites6 = [TerminalSymbol.F1] :=
  rfl

theorem foldedSites6_hitSymbolsAt_five :
    hitSymbolsAt 5 foldedSites6 = [TerminalSymbol.F1] :=
  rfl

theorem foldedSites4_chronologicalTrace_by_slots :
    chronologicalTrace 4 foldedSites4 =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F1] :=
  rfl

theorem foldedSites6_chronologicalTrace_by_slots :
    chronologicalTrace 6 foldedSites6 =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0,
        TerminalSymbol.F1, TerminalSymbol.F1] :=
  rfl

theorem foldedSites4_chronologicalTrace :
    chronologicalTrace 4 foldedSites4 = terminalTrace4 := by
  rfl

theorem foldedSites6_chronologicalTrace :
    chronologicalTrace 6 foldedSites6 = terminalTrace6 := by
  rfl

theorem foldedSites4_singleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (chronologicalTrace 4 foldedSites4)) := by
  rw [foldedSites4_chronologicalTrace]
  exact terminalTrace4_singleCycle

theorem foldedSites6_singleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (chronologicalTrace 6 foldedSites6)) := by
  rw [foldedSites6_chronologicalTrace]
  exact terminalTrace6_singleCycle

end FoldedSiteTrace

export FoldedSiteTrace
  (FoldedRole FoldedCoord TerminalHit FoldedSwitchingSite
   foldedCoord foldedCoordCode allCodesMatch hitSymbolsAt chronologicalTrace
   foldedSiteRoles foldedSiteCodes foldedSiteHits foldedRoleTable
   foldedSites4 foldedSites6 foldedSites4_codes foldedSites6_codes
   foldedSites4_length foldedSites6_length
   foldedSites4_roles foldedSites6_roles
   foldedSites4_roles_nodup foldedSites6_roles_nodup
   foldedSites4_codeList foldedSites6_codeList
   foldedSites4_hits foldedSites6_hits
   foldedSites4_hitSymbolsAt_zero foldedSites4_hitSymbolsAt_one
   foldedSites4_hitSymbolsAt_two foldedSites4_hitSymbolsAt_three
   foldedSites6_hitSymbolsAt_zero foldedSites6_hitSymbolsAt_one
   foldedSites6_hitSymbolsAt_two foldedSites6_hitSymbolsAt_three
   foldedSites6_hitSymbolsAt_four foldedSites6_hitSymbolsAt_five
   foldedSites4_chronologicalTrace_by_slots
   foldedSites6_chronologicalTrace_by_slots
   foldedSites4_chronologicalTrace foldedSites6_chronologicalTrace
   foldedSites4_singleCycle foldedSites6_singleCycle)

end EvenV11
