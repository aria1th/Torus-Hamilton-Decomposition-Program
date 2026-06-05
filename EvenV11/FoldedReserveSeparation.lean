import EvenV11.FoldedSiteTrace

namespace EvenV11
namespace FoldedReserveSeparation

structure CodedCoord (m : Nat) where
  coord : FoldedCoord m
  code : Nat
  deriving DecidableEq, Repr

inductive ReserveRole where
  | U0
  | U1
  | U2
  | U1c
  | U2c
  | U3c
  | U4c
  | U5c
  | U6c
  | Ustar
  deriving DecidableEq, Repr

structure ReserveState (m : Nat) where
  role : ReserveRole
  coord : FoldedCoord m
  code : Nat
  deriving DecidableEq, Repr

def codedCoordMatches {m : Nat} [NeZero m] (entry : CodedCoord m) :
    Bool :=
  entry.code == foldedCoordCode entry.coord

def allCodedCoordsMatch {m : Nat} [NeZero m]
    (entries : List (CodedCoord m)) : Prop :=
  entries.all codedCoordMatches = true

def reserveCodeMatches {m : Nat} [NeZero m] (entry : ReserveState m) :
    Bool :=
  entry.code == foldedCoordCode entry.coord

def allReserveCodesMatch {m : Nat} [NeZero m]
    (entries : List (ReserveState m)) : Prop :=
  entries.all reserveCodeMatches = true

def siteCoords {m : Nat} (sites : List (FoldedSwitchingSite m)) :
    List (FoldedCoord m) :=
  sites.map fun site => site.coord

def codedCoords {m : Nat} (entries : List (CodedCoord m)) :
    List (FoldedCoord m) :=
  entries.map CodedCoord.coord

def reserveCoords {m : Nat} (entries : List (ReserveState m)) :
    List (FoldedCoord m) :=
  entries.map ReserveState.coord

def codedCoordCodes {m : Nat} (entries : List (CodedCoord m)) :
    List Nat :=
  entries.map CodedCoord.code

def reserveRoles {m : Nat} (entries : List (ReserveState m)) :
    List ReserveRole :=
  entries.map ReserveState.role

def reserveStateCodes {m : Nat} (entries : List (ReserveState m)) :
    List Nat :=
  entries.map ReserveState.code

def qzSeparated {m : Nat} (point site : FoldedCoord m) : Bool :=
  (point.q != site.q) || (point.z != site.z)

def qzSeparatedFromSites {m : Nat}
    (points : List (FoldedCoord m)) (sites : List (FoldedSwitchingSite m)) :
    Prop :=
  points.all (fun point =>
    sites.all (fun site => qzSeparated point site.coord)) = true

def qProjectionAbsent {m : Nat} (q : TerminalQ m)
    (coords : List (FoldedCoord m)) : Prop :=
  coords.all (fun coord => coord.q != q) = true

def allQProjection {m : Nat} (q : TerminalQ m)
    (coords : List (FoldedCoord m)) : Prop :=
  coords.all (fun coord => coord.q == q) = true

def reserveRoleTable : List ReserveRole :=
  [ReserveRole.U0, ReserveRole.U1, ReserveRole.U2, ReserveRole.U1c,
    ReserveRole.U2c, ReserveRole.U3c, ReserveRole.U4c, ReserveRole.U5c,
    ReserveRole.U6c, ReserveRole.Ustar]

def protected4 : List (CodedCoord 4) :=
  [ { coord := foldedCoord 0 1 0 1 0 0, code := 68 },
    { coord := foldedCoord 2 1 3 1 3 0, code := 886 },
    { coord := foldedCoord 0 2 0 1 1 1, code := 1352 },
    { coord := foldedCoord 3 1 0 1 0 3, code := 3143 } ]

def protected6 : List (CodedCoord 6) :=
  [ { coord := foldedCoord 0 5 2 1 2 0, code := 2910 },
    { coord := foldedCoord 0 0 3 2 2 1, code := 10908 },
    { coord := foldedCoord 0 4 1 0 2 5, code := 41532 },
    { coord := foldedCoord 5 5 1 5 2 5, code := 42623 } ]

def reserves4 : List (ReserveState 4) :=
  [ { role := ReserveRole.U0,
      coord := foldedCoord 0 0 3 3 0 0, code := 240 },
    { role := ReserveRole.U1,
      coord := foldedCoord 1 0 3 3 0 0, code := 241 },
    { role := ReserveRole.U2,
      coord := foldedCoord 2 0 3 3 0 0, code := 242 },
    { role := ReserveRole.U1c,
      coord := foldedCoord 3 0 3 3 0 0, code := 243 },
    { role := ReserveRole.U2c,
      coord := foldedCoord 0 1 3 3 0 0, code := 244 },
    { role := ReserveRole.U3c,
      coord := foldedCoord 1 1 3 3 0 0, code := 245 },
    { role := ReserveRole.U4c,
      coord := foldedCoord 2 1 3 3 0 0, code := 246 },
    { role := ReserveRole.U5c,
      coord := foldedCoord 3 1 3 3 0 0, code := 247 },
    { role := ReserveRole.U6c,
      coord := foldedCoord 0 2 3 3 0 0, code := 248 },
    { role := ReserveRole.Ustar,
      coord := foldedCoord 1 2 3 3 0 0, code := 249 } ]

def reserves6 : List (ReserveState 6) :=
  [ { role := ReserveRole.U0,
      coord := foldedCoord 0 0 5 5 0 0, code := 1260 },
    { role := ReserveRole.U1,
      coord := foldedCoord 1 0 5 5 0 0, code := 1261 },
    { role := ReserveRole.U2,
      coord := foldedCoord 2 0 5 5 0 0, code := 1262 },
    { role := ReserveRole.U1c,
      coord := foldedCoord 3 0 5 5 0 0, code := 1263 },
    { role := ReserveRole.U2c,
      coord := foldedCoord 4 0 5 5 0 0, code := 1264 },
    { role := ReserveRole.U3c,
      coord := foldedCoord 5 0 5 5 0 0, code := 1265 },
    { role := ReserveRole.U4c,
      coord := foldedCoord 0 1 5 5 0 0, code := 1266 },
    { role := ReserveRole.U5c,
      coord := foldedCoord 1 1 5 5 0 0, code := 1267 },
    { role := ReserveRole.U6c,
      coord := foldedCoord 2 1 5 5 0 0, code := 1268 },
    { role := ReserveRole.Ustar,
      coord := foldedCoord 3 1 5 5 0 0, code := 1269 } ]

theorem protected4_codes :
    allCodedCoordsMatch protected4 := by
  rfl

theorem protected6_codes :
    allCodedCoordsMatch protected6 := by
  rfl

theorem reserves4_codes :
    allReserveCodesMatch reserves4 := by
  rfl

theorem reserves6_codes :
    allReserveCodesMatch reserves6 := by
  rfl

theorem protected4_length :
    protected4.length = 4 :=
  rfl

theorem protected6_length :
    protected6.length = 4 :=
  rfl

theorem reserves4_length :
    reserves4.length = 10 :=
  rfl

theorem reserves6_length :
    reserves6.length = 10 :=
  rfl

theorem protected4_codeList :
    codedCoordCodes protected4 = [68, 886, 1352, 3143] :=
  rfl

theorem protected6_codeList :
    codedCoordCodes protected6 = [2910, 10908, 41532, 42623] :=
  rfl

theorem protected4_nodup :
    (codedCoords protected4).Nodup := by
  decide

theorem protected6_nodup :
    (codedCoords protected6).Nodup := by
  decide

theorem reserves4_roles :
    reserveRoles reserves4 = reserveRoleTable :=
  rfl

theorem reserves6_roles :
    reserveRoles reserves6 = reserveRoleTable :=
  rfl

theorem reserves4_roles_nodup :
    (reserveRoles reserves4).Nodup := by
  decide

theorem reserves6_roles_nodup :
    (reserveRoles reserves6).Nodup := by
  decide

theorem reserves4_codeList :
    reserveStateCodes reserves4 =
      [240, 241, 242, 243, 244, 245, 246, 247, 248, 249] :=
  rfl

theorem reserves6_codeList :
    reserveStateCodes reserves6 =
      [1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268,
        1269] :=
  rfl

theorem protected4_qzSeparatedFromSites :
    qzSeparatedFromSites (codedCoords protected4) foldedSites4 := by
  rfl

theorem protected6_qzSeparatedFromSites :
    qzSeparatedFromSites (codedCoords protected6) foldedSites6 := by
  rfl

theorem reserves4_nodup :
    (reserveCoords reserves4).Nodup := by
  decide

theorem reserves6_nodup :
    (reserveCoords reserves6).Nodup := by
  decide

theorem reserves4_terminalProjection :
    allQProjection ((3 : ZMod 4), (3 : ZMod 4))
      (reserveCoords reserves4) := by
  rfl

theorem reserves6_terminalProjection :
    allQProjection ((5 : ZMod 6), (5 : ZMod 6))
      (reserveCoords reserves6) := by
  rfl

theorem reserveProjection4_absent_from_sites :
    qProjectionAbsent ((3 : ZMod 4), (3 : ZMod 4))
      (siteCoords foldedSites4) := by
  rfl

theorem reserveProjection6_absent_from_sites :
    qProjectionAbsent ((5 : ZMod 6), (5 : ZMod 6))
      (siteCoords foldedSites6) := by
  rfl

theorem reserveProjection4_absent_from_protected :
    qProjectionAbsent ((3 : ZMod 4), (3 : ZMod 4))
      (codedCoords protected4) := by
  rfl

theorem reserveProjection6_absent_from_protected :
    qProjectionAbsent ((5 : ZMod 6), (5 : ZMod 6))
      (codedCoords protected6) := by
  rfl

end FoldedReserveSeparation

export FoldedReserveSeparation
  (CodedCoord ReserveRole ReserveState
   protected4 protected6 reserves4 reserves6
   siteCoords codedCoords reserveCoords
   codedCoordCodes reserveRoles reserveStateCodes reserveRoleTable
   codedCoordMatches allCodedCoordsMatch reserveCodeMatches
   allReserveCodesMatch qzSeparated qzSeparatedFromSites
   qProjectionAbsent allQProjection
   protected4_codes protected6_codes reserves4_codes reserves6_codes
   protected4_length protected6_length reserves4_length reserves6_length
   protected4_codeList protected6_codeList
   protected4_nodup protected6_nodup
   reserves4_roles reserves6_roles
   reserves4_roles_nodup reserves6_roles_nodup
   reserves4_codeList reserves6_codeList
   protected4_qzSeparatedFromSites protected6_qzSeparatedFromSites
   reserves4_nodup reserves6_nodup
   reserves4_terminalProjection reserves6_terminalProjection
   reserveProjection4_absent_from_sites reserveProjection6_absent_from_sites
   reserveProjection4_absent_from_protected
   reserveProjection6_absent_from_protected)

end EvenV11
