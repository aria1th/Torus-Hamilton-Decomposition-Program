import EvenV11.FoldedCommonEdgeWitness

namespace EvenV11
namespace EndpointMarkedTransferBridge

def singletonCommonEdgeWitnessInput {m : Nat} [NeZero m]
    (witness : SingletonCommonEdgeWitness m)
    (sites : List (FoldedSwitchingSite m)) : Prop :=
  codedCoordMatches witness.selector = true ∧
  codedCoordMatches witness.commonImage = true ∧
  witness.selector ∈ witness.protectedSet ∧
  witness.commonImage ∈ witness.protectedSet ∧
  witness.selector ≠ witness.commonImage ∧
  witness.protectedSet.length = witness.protectedSize ∧
  (codedCoords witness.protectedSet).Nodup ∧
  qzSeparatedFromSites (codedCoords witness.protectedSet) sites ∧
  Shared.IsSingleCycleMap
    (wordEval (terminalSymbolStep m) witness.terminalTrace)

def foldedReserveRenewalInput {m : Nat} [NeZero m]
    (reserves : List (ReserveState m))
    (sites : List (FoldedSwitchingSite m))
    (protectedSet : List (CodedCoord m))
    (projection : TerminalQ m) : Prop :=
  allReserveCodesMatch reserves ∧
  reserves.length = 10 ∧
  reserveRoles reserves = reserveRoleTable ∧
  (reserveRoles reserves).Nodup ∧
  (reserveCoords reserves).Nodup ∧
  allQProjection projection (reserveCoords reserves) ∧
  qProjectionAbsent projection (siteCoords sites) ∧
  qProjectionAbsent projection (codedCoords protectedSet)

def foldedEndpointMarkedTransferInput4 : Prop :=
  singletonCommonEdgeWitnessInput singletonCommonEdgeWitness4 foldedSites4 ∧
  foldedReserveRenewalInput reserves4 foldedSites4 protected4
    ((3 : ZMod 4), (3 : ZMod 4))

def foldedEndpointMarkedTransferInput6 : Prop :=
  singletonCommonEdgeWitnessInput singletonCommonEdgeWitness6 foldedSites6 ∧
  foldedReserveRenewalInput reserves6 foldedSites6 protected6
    ((5 : ZMod 6), (5 : ZMod 6))

def foldedEndpointMarkedTransferInputAudit : Prop :=
  foldedEndpointMarkedTransferInput4 ∧
  foldedEndpointMarkedTransferInput6

theorem foldedEndpointMarkedTransferInput4_holds :
    foldedEndpointMarkedTransferInput4 :=
  ⟨⟨singletonCommonEdgeWitness4_selectorCodeMatches,
      singletonCommonEdgeWitness4_commonImageCodeMatches,
      singletonCommonEdgeWitness4_selector_mem_protected,
      singletonCommonEdgeWitness4_commonImage_mem_protected,
      singletonCommonEdgeWitness4_selector_ne_commonImage,
      singletonCommonEdgeWitness4_protectedSize,
      singletonCommonEdgeWitness4_protected_nodup,
      singletonCommonEdgeWitness4_protectedSeparatedFromSites,
      singletonCommonEdgeWitness4_traceSingleCycle_fromFoldedSites⟩,
    ⟨reserves4_codes,
      reserves4_length,
      reserves4_roles,
      reserves4_roles_nodup,
      reserves4_nodup,
      reserves4_terminalProjection,
      reserveProjection4_absent_from_sites,
      reserveProjection4_absent_from_protected⟩⟩

theorem foldedEndpointMarkedTransferInput6_holds :
    foldedEndpointMarkedTransferInput6 :=
  ⟨⟨singletonCommonEdgeWitness6_selectorCodeMatches,
      singletonCommonEdgeWitness6_commonImageCodeMatches,
      singletonCommonEdgeWitness6_selector_mem_protected,
      singletonCommonEdgeWitness6_commonImage_mem_protected,
      singletonCommonEdgeWitness6_selector_ne_commonImage,
      singletonCommonEdgeWitness6_protectedSize,
      singletonCommonEdgeWitness6_protected_nodup,
      singletonCommonEdgeWitness6_protectedSeparatedFromSites,
      singletonCommonEdgeWitness6_traceSingleCycle_fromFoldedSites⟩,
    ⟨reserves6_codes,
      reserves6_length,
      reserves6_roles,
      reserves6_roles_nodup,
      reserves6_nodup,
      reserves6_terminalProjection,
      reserveProjection6_absent_from_sites,
      reserveProjection6_absent_from_protected⟩⟩

theorem foldedEndpointMarkedTransferInputAudit_holds :
    foldedEndpointMarkedTransferInputAudit :=
  ⟨foldedEndpointMarkedTransferInput4_holds,
    foldedEndpointMarkedTransferInput6_holds⟩

end EndpointMarkedTransferBridge

export EndpointMarkedTransferBridge
  (foldedEndpointMarkedTransferInput4_holds
   foldedEndpointMarkedTransferInput6_holds
   foldedEndpointMarkedTransferInputAudit_holds)

end EvenV11
