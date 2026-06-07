import EvenV11.Basic
import EvenV11.ReturnCalculus
import EvenV11.UnitCarry
import EvenV11.EndpointCompletion
import EvenV11.ProjectionKernel
import EvenV11.GuideLocality
import EvenV11.Switching
import EvenV11.AffineSeparation
import EvenV11.PhaseDoubling
import EvenV11.SupportSeparation
import EvenV11.PhaseSupport
import EvenV11.WordSkew
import EvenV11.EndpointRowPlacement
import EvenV11.PhaseWordSupport
import EvenV11.PhaseProductSupport
import EvenV11.PhaseProductRealizationBridge
import EvenV11.EndpointReservePlacement
import EvenV11.TerminalWords
import EvenV11.FiniteCertificate
import EvenV11.TerminalA2LowMod
import EvenV11.D54Reset
import EvenV11.D54ResetData
import EvenV11.FoldedSiteTrace
import EvenV11.FoldedReserveSeparation
import EvenV11.FoldedCommonEdgeWitness
import EvenV11.EndpointMarkedTransferBridge
import EvenV11.FiniteAudit
import EvenV11.FiniteAuditBridge
import EvenV11.TypeA.TreeIncidence
import EvenV11.TypeA.RootedParentMap
import EvenV11.TypeA.CoforestExample
import EvenV11.TypeA.AnchorBridge
import EvenV11.HighEvenSuccessorBridge
import EvenV11.FinalInductionBridge
import EvenV11.FinalRangeBookkeepingBridge
import EvenV11.FinalInductionSchemeBridge
import EvenV11.FinalSchemeProjectionBridge
import EvenV11.FinalConstructionArrowBridge
import EvenV11.FinalArrowObligationBridge
import EvenV11.FinalTargetPredicateBridge
import EvenV11.FinalTargetRootFlatCertificateBridge
import EvenV11.FinalTargetD2BaseBridge
import EvenV11.FinalTargetBaseAssemblyBridge
import EvenV11.FinalTargetGrowthAssemblyBridge
import EvenV11.FinalTargetLowBaseBridge
import EvenV11.FinalTargetD3BaseBridge
import EvenV11.FinalTargetPhaseDoublingBridge
import EvenV11.FinalTargetRemainingBridge
import EvenV11.FinalTargetPostPhaseGrowthBridge
import EvenV11.FinalTargetSixObligationBridge
import EvenV11.FinalTargetLowBaseCertificateBridge
import EvenV11.FinalTargetEndpointCertificateBridge
import EvenV11.FinalTargetHighEvenCertificateBridge
import EvenV11.FinalTargetPhaseProductCertificateBridge
import EvenV11.FinalTargetCertificateChecklistBridge
import EvenV11.FinalTargetCertificateInputInventoryBridge
import EvenV11.FinalTargetD3RootFlatCertificateBridge
import EvenV11.FinalTargetLowBaseRootFlatCertificateBridge

namespace EvenV11

theorem edgePartitionOfRowLatin_closed
    {Color Direction RootState : Type*} {m : Nat}
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) :
    S.edgePartition :=
  edgePartitionOfRowLatin hRow

theorem fullStepsHamiltonianOfReturn_closed
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    S.fullStepsHamiltonian :=
  fullStepsHamiltonianOfReturn hLayer hReturn

theorem rootFlatReturnCriterion_closed
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    Shared.RootFlatReturnCriterion Color Direction RootState m :=
  rootFlatReturnCriterion hRow hLayer hReturn

theorem rootFlatLayeredHamiltonian_closed
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    Shared.RootFlatLayeredHamiltonDecomposition
      Color Direction RootState m :=
  rootFlatLayeredHamiltonian hRow hLayer hReturn

theorem unitCarrySingleCycle_closed
    {Base : Type*} {m : Nat} [NeZero m]
    (baseStep : Base → Base) (carry : Base → ZMod m)
    (base : Base) (period : Nat) (a : ZMod m)
    (hbase : Function.Bijective baseStep)
    (hreturnBase : (baseStep^[period]) base = base)
    (hbaseCover : ∀ b : Base, ∃ k : Nat,
      k < period ∧ (baseStep^[k]) base = b)
    (ha : IsUnit a)
    (hcarry :
      Shared.skewFiberAdditiveCarry baseStep carry period base = a) :
    Shared.IsSingleCycleMap (additiveSkewMap baseStep carry) :=
  unitCarrySingleCycle baseStep carry base period a
    hbase hreturnBase hbaseCover ha hcarry

theorem rankUnitCarrySingleCycle_closed
    {Base : Type*} [Fintype Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (carry : Base → ZMod m) (base : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hunit : IsUnit (∑ x : Base, carry x)) :
    Shared.IsSingleCycleMap (additiveSkewMap baseStep carry) :=
  rankUnitCarrySingleCycle baseStep rank carry base hstep hunit

theorem pointCarry_closed
    {Base : Type*} [DecidableEq Base]
    {m : Nat} (crossing : Base) (a : ZMod m) :
    @pointCarry Base inferInstance m crossing a =
      fun x : Base => if x = crossing then a else 0 :=
  rfl

theorem pointCarry_crossing_closed
    {Base : Type*} [DecidableEq Base]
    {m : Nat} (crossing : Base) (a : ZMod m) :
    @pointCarry Base inferInstance m crossing a crossing = a :=
  pointCarry_crossing crossing a

theorem pointCarry_of_ne_closed
    {Base : Type*} [DecidableEq Base]
    {m : Nat} {crossing x : Base} (a : ZMod m) (hx : x ≠ crossing) :
    @pointCarry Base inferInstance m crossing a x = 0 :=
  pointCarry_of_ne a hx

theorem pointCarrySum_closed
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) (a : ZMod m) :
    (∑ x : Base, @pointCarry Base inferInstance m crossing a x) = a :=
  pointCarrySum crossing a

theorem pointCarryUnit_closed
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) {a : ZMod m} (ha : IsUnit a) :
    IsUnit (∑ x : Base, @pointCarry Base inferInstance m crossing a x) :=
  pointCarryUnit crossing ha

theorem pointCarrySingleCycle_closed
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base) (a : ZMod m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (ha : IsUnit a) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (@pointCarry Base inferInstance m crossing a)) :=
  pointCarrySingleCycle baseStep rank base crossing a hstep ha

theorem singlePointCarry_eq_pointCarry_closed
    {Base : Type*} [DecidableEq Base] {m : Nat} (crossing : Base) :
    (fun x : Base => if x = crossing then (1 : ZMod m) else 0) =
      @pointCarry Base inferInstance m crossing (1 : ZMod m) :=
  singlePointCarry_eq_pointCarry crossing

theorem negativeSinglePointCarry_eq_pointCarry_closed
    {Base : Type*} [DecidableEq Base] {m : Nat} (crossing : Base) :
    (fun x : Base => if x = crossing then (-1 : ZMod m) else 0) =
      @pointCarry Base inferInstance m crossing (-1 : ZMod m) :=
  negativeSinglePointCarry_eq_pointCarry crossing

theorem singlePointCarrySingleCycle_pointCarry_closed
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (@pointCarry Base inferInstance m crossing (1 : ZMod m))) :=
  singlePointCarrySingleCycle_pointCarry baseStep rank base crossing hstep

theorem negativeSinglePointCarrySingleCycle_pointCarry_closed
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (@pointCarry Base inferInstance m crossing (-1 : ZMod m))) :=
  negativeSinglePointCarrySingleCycle_pointCarry
    baseStep rank base crossing hstep

theorem singlePointCarrySum_closed
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    (∑ x : Base, if x = crossing then (1 : ZMod m) else 0) = 1 :=
  singlePointCarrySum crossing

theorem negativeSinglePointCarrySum_closed
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    (∑ x : Base, if x = crossing then (-1 : ZMod m) else 0) = -1 :=
  negativeSinglePointCarrySum crossing

theorem singlePointCarryUnit_closed
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    IsUnit (∑ x : Base, if x = crossing then (1 : ZMod m) else 0) :=
  singlePointCarryUnit crossing

theorem negativeSinglePointCarryUnit_closed
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    IsUnit (∑ x : Base, if x = crossing then (-1 : ZMod m) else 0) :=
  negativeSinglePointCarryUnit crossing

theorem singlePointCarrySingleCycle_closed
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (fun x : Base => if x = crossing then (1 : ZMod m) else 0)) :=
  singlePointCarrySingleCycle baseStep rank base crossing hstep

theorem negativeSinglePointCarrySingleCycle_closed
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (fun x : Base => if x = crossing then (-1 : ZMod m) else 0)) :=
  negativeSinglePointCarrySingleCycle baseStep rank base crossing hstep

theorem squareSubOneCoprimeSelf_closed
    (m : Nat) [NeZero m] :
    Nat.Coprime (m * m - 1) m :=
  squareSubOneCoprimeSelf m

theorem squareSubOneCoprimePow_closed
    (m k : Nat) [NeZero m] :
    Nat.Coprime (m * m - 1) (m ^ k) :=
  squareSubOneCoprimePow m k

theorem squareSubOneUnitZModPow_closed
    (m k : Nat) [NeZero m] :
    IsUnit (((m * m - 1 : Nat) : ZMod (m ^ k))) :=
  squareSubOneUnitZModPow m k

theorem singletonExponentSum_closed
    {Terminal : Type*} [Fintype Terminal] [DecidableEq Terminal]
    {M : Nat} (q0 : Terminal) :
    (∑ q : Terminal, if q = q0 then (1 : ZMod M) else 0) = 1 :=
  singletonExponentSum q0

theorem complementSingletonExponentSum_closed
    {Terminal : Type*} [Fintype Terminal] [DecidableEq Terminal]
    {M : Nat} (q0 : Terminal) :
    (∑ q : Terminal, if q = q0 then (0 : ZMod M) else 1) =
      ((Fintype.card Terminal - 1 : Nat) : ZMod M) :=
  complementSingletonExponentSum q0

theorem productExponentSingleCycle_closed
    {Terminal : Type*} [Fintype Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (exponent : Terminal → ZMod M) (base : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1)
    (hunit : IsUnit (∑ q : Terminal, exponent q)) :
    Shared.IsSingleCycleMap (productExponentMap terminalStep exponent) :=
  productExponentSingleCycle terminalStep terminalRank exponent base
    hstep hunit

theorem pointProductExponentSingleCycle_closed
    {Terminal : Type*} [Finite Terminal] [DecidableEq Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (base q0 : Terminal) (a : ZMod M)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1)
    (ha : IsUnit a) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (@pointCarry Terminal inferInstance M q0 a)) :=
  pointProductExponentSingleCycle terminalStep terminalRank base q0
    a hstep ha

theorem singletonPointProductExponentSingleCycle_closed
    {Terminal : Type*} [Finite Terminal] [DecidableEq Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (base q0 : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (@pointCarry Terminal inferInstance M q0 (1 : ZMod M))) :=
  singletonPointProductExponentSingleCycle terminalStep terminalRank
    base q0 hstep

theorem singletonProductExponentSingleCycle_closed
    {Terminal : Type*} [Finite Terminal] [DecidableEq Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (base q0 : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (fun q : Terminal => if q = q0 then (1 : ZMod M) else 0)) :=
  singletonProductExponentSingleCycle terminalStep terminalRank
    base q0 hstep

theorem complementSingletonProductExponentSingleCycle_closed
    {Terminal : Type*} [Fintype Terminal] [DecidableEq Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (base q0 : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1)
    (hunit :
      IsUnit
        (∑ q : Terminal, if q = q0 then (0 : ZMod M) else 1)) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (fun q : Terminal => if q = q0 then (0 : ZMod M) else 1)) :=
  complementSingletonProductExponentSingleCycle terminalStep terminalRank
    base q0 hstep hunit

theorem squareSubOneProductExponentSingleCycle_closed
    {Terminal : Type*} [Fintype Terminal]
    {N m k : Nat} [NeZero N] [NeZero m]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (exponent : Terminal → ZMod (m ^ k)) (base : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1)
    (hsum :
      (∑ q : Terminal, exponent q) =
        ((m * m - 1 : Nat) : ZMod (m ^ k))) :
    Shared.IsSingleCycleMap (productExponentMap terminalStep exponent) :=
  squareSubOneProductExponentSingleCycle terminalStep terminalRank
    exponent base hstep hsum

theorem complementSingletonSquareProductExponentSingleCycle_closed
    {Terminal : Type*} [Fintype Terminal] [DecidableEq Terminal]
    {N m k : Nat} [NeZero N] [NeZero m]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (base q0 : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1)
    (hcard : Fintype.card Terminal = m * m) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (fun q : Terminal => if q = q0 then (0 : ZMod (m ^ k)) else 1)) :=
  complementSingletonSquareProductExponentSingleCycle terminalStep
    terminalRank base q0 hstep hcard

theorem cyclicCompletionRow_closed
    {n : Nat} (shift k : ZMod n) :
    cyclicCompletionRow shift k = k + shift :=
  rfl

theorem cyclicCompletionTail_closed
    {n : Nat} (target shift : ZMod n) :
    cyclicCompletionTail target shift = target - shift :=
  rfl

theorem rowIncidence_closed
    {Coord : Type*} {m : Nat}
    (coordRead : Coord → ZMod m) (row : Coord → Coord)
    (tail : Coord) :
    rowIncidence coordRead row tail =
      coordRead (row tail) - coordRead tail :=
  rfl

theorem targetIndicatorCoordRead_closed
    {n m : Nat} (target coord : ZMod n) :
    @targetIndicatorCoordRead n m target coord =
      if coord = target then 1 else 0 :=
  rfl

theorem completionCarry_closed
    {Base Coord : Type*} {m : Nat}
    (coordRead : Coord → ZMod m) (row : Coord → Coord)
    (tail : Base → Coord) :
    completionCarry coordRead row tail =
      fun x => rowIncidence coordRead row (tail x) :=
  rfl

theorem rowIncidence_eq_zero_of_eq_closed
    {Coord : Type*} {m : Nat}
    {coordRead : Coord → ZMod m} {row : Coord → Coord} {tail : Coord}
    (hread : coordRead (row tail) = coordRead tail) :
    rowIncidence coordRead row tail = 0 :=
  rowIncidence_eq_zero_of_eq hread

theorem targetIndicatorCoordRead_target_closed
    {n m : Nat} (target : ZMod n) :
    @targetIndicatorCoordRead n m target target = 1 :=
  targetIndicatorCoordRead_target target

theorem targetIndicatorCoordRead_of_ne_closed
    {n m : Nat} (target coord : ZMod n) (hcoord : coord ≠ target) :
    @targetIndicatorCoordRead n m target coord = 0 :=
  targetIndicatorCoordRead_of_ne target coord hcoord

theorem carry_eq_pointCarry_of_crossing_and_off_closed
    {Base : Type*} [DecidableEq Base] {m : Nat}
    (carry : Base → ZMod m) (crossing : Base) (epsilon : ZMod m)
    (hcross : carry crossing = epsilon)
    (hoff : ∀ x : Base, x ≠ crossing → carry x = 0) :
    carry = pointCarry crossing epsilon :=
  carry_eq_pointCarry_of_crossing_and_off
    carry crossing epsilon hcross hoff

theorem completionCarryCertificate_eq_pointCarry_closed
    {Base Coord : Type*} [DecidableEq Base] {m : Nat}
    (C : CompletionCarryCertificate Base Coord m) :
    completionCarry C.coordRead C.row C.tail =
      pointCarry C.crossing C.epsilon :=
  completionCarryCertificate_eq_pointCarry C

theorem completionCarryCertificate_singleCycle_closed
    {Base Coord : Type*} [Finite Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base : Base) (C : CompletionCarryCertificate Base Coord m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hepsilon : IsUnit C.epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (completionCarry C.coordRead C.row C.tail)) :=
  completionCarryCertificate_singleCycle
    baseStep rank base C hstep hepsilon

theorem cyclicCompletionRow_bijective_closed
    {n : Nat} (shift : ZMod n) :
    Function.Bijective (cyclicCompletionRow shift) :=
  cyclicCompletionRow_bijective shift

theorem cyclicCompletionRow_tail_closed
    {n : Nat} (target shift : ZMod n) :
    cyclicCompletionRow shift (cyclicCompletionTail target shift) =
      target :=
  cyclicCompletionRow_tail target shift

theorem cyclicCompletionTail_unique_closed
    {n : Nat} {target shift k : ZMod n}
    (hk : cyclicCompletionRow shift k = target) :
    k = cyclicCompletionTail target shift :=
  cyclicCompletionTail_unique hk

theorem cyclicCompletionRow_tail_iff_closed
    {n : Nat} {target shift k : ZMod n} :
    cyclicCompletionRow shift k = target ↔
      k = cyclicCompletionTail target shift :=
  cyclicCompletionRow_tail_iff

theorem cyclicCompletionRow_moved_of_shift_ne_zero_closed
    {n : Nat} {shift k : ZMod n} (hshift : shift ≠ 0) :
    cyclicCompletionRow shift k ≠ k :=
  cyclicCompletionRow_moved_of_shift_ne_zero hshift

theorem cyclicCompletionTail_ne_target_of_shift_ne_zero_closed
    {n : Nat} {target shift : ZMod n} (hshift : shift ≠ 0) :
    cyclicCompletionTail target shift ≠ target :=
  cyclicCompletionTail_ne_target_of_shift_ne_zero hshift

theorem targetIndicatorCoordRead_cyclicCompletionTail_closed
    {n m : Nat} {target shift : ZMod n} (hshift : shift ≠ 0) :
    @targetIndicatorCoordRead n m target
      (cyclicCompletionTail target shift) = 0 :=
  targetIndicatorCoordRead_cyclicCompletionTail hshift

theorem cyclicCompletionRowIncidence_tail_closed
    {n m : Nat} (target shift : ZMod n)
    (coordRead : ZMod n → ZMod m) {epsilon : ZMod m}
    (htarget : coordRead target = epsilon)
    (htail :
      coordRead (cyclicCompletionTail target shift) = 0) :
    rowIncidence coordRead (cyclicCompletionRow shift)
      (cyclicCompletionTail target shift) = epsilon :=
  cyclicCompletionRowIncidence_tail
    target shift coordRead htarget htail

theorem cyclicCompletionRowIncidence_eq_zero_of_read_eq_closed
    {n m : Nat} (shift : ZMod n) (coordRead : ZMod n → ZMod m)
    {tail : ZMod n}
    (hread :
      coordRead (cyclicCompletionRow shift tail) = coordRead tail) :
    rowIncidence coordRead (cyclicCompletionRow shift) tail = 0 :=
  cyclicCompletionRowIncidence_eq_zero_of_read_eq
    shift coordRead hread

theorem cyclicCompletionRowIncidence_targetIndicator_tail_closed
    {n m : Nat} {target shift : ZMod n}
    (hshift : shift ≠ 0) :
    rowIncidence (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift)
      (cyclicCompletionTail target shift) = 1 :=
  cyclicCompletionRowIncidence_targetIndicator_tail hshift

theorem cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_ne_target_closed
    {n m : Nat} (target shift tail : ZMod n)
    (htail : tail ≠ target)
    (hrow : cyclicCompletionRow shift tail ≠ target) :
    rowIncidence (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail = 0 :=
  cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_ne_target
    target shift tail htail hrow

theorem completionTargetAvoids_closed
    {n : Nat} {target shift tail : ZMod n} :
    completionTargetAvoids target shift tail =
      (tail ≠ target ∧ cyclicCompletionRow shift tail ≠ target) :=
  rfl

theorem completionTargetAvoids_tail_ne_target_closed
    {n : Nat} {target shift tail : ZMod n}
    (havoid : completionTargetAvoids target shift tail) :
    tail ≠ target :=
  completionTargetAvoids_tail_ne_target havoid

theorem completionTargetAvoids_row_ne_target_closed
    {n : Nat} {target shift tail : ZMod n}
    (havoid : completionTargetAvoids target shift tail) :
    cyclicCompletionRow shift tail ≠ target :=
  completionTargetAvoids_row_ne_target havoid

theorem cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_avoids_closed
    {n m : Nat} {target shift tail : ZMod n}
    (havoid : completionTargetAvoids target shift tail) :
    rowIncidence (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail = 0 :=
  cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_avoids havoid

theorem cyclicCompletionCarry_eq_pointCarry_closed
    {Base : Type*} [DecidableEq Base] {n m : Nat}
    (target shift : ZMod n) (coordRead : ZMod n → ZMod m)
    (tail : Base → ZMod n) (crossing : Base) (epsilon : ZMod m)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htarget : coordRead target = epsilon)
    (htail :
      coordRead (cyclicCompletionTail target shift) = 0)
    (hoff : ∀ x : Base, x ≠ crossing →
      rowIncidence coordRead (cyclicCompletionRow shift) (tail x) = 0) :
    completionCarry coordRead (cyclicCompletionRow shift) tail =
      pointCarry crossing epsilon :=
  cyclicCompletionCarry_eq_pointCarry
    target shift coordRead tail crossing epsilon
    hcrossTail htarget htail hoff

theorem cyclicCompletionCarrySingleCycle_closed
    {Base : Type*} [Finite Base]
    {n N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (target shift : ZMod n) (coordRead : ZMod n → ZMod m)
    (tail : Base → ZMod n) (epsilon : ZMod m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htarget : coordRead target = epsilon)
    (htail :
      coordRead (cyclicCompletionTail target shift) = 0)
    (hoff : ∀ x : Base, x ≠ crossing →
      rowIncidence coordRead (cyclicCompletionRow shift) (tail x) = 0)
    (hepsilon : IsUnit epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (completionCarry coordRead (cyclicCompletionRow shift) tail)) :=
  cyclicCompletionCarrySingleCycle
    baseStep rank base crossing target shift coordRead tail epsilon
    hstep hcrossTail htarget htail hoff hepsilon

theorem finCompletionBaseStep_closed
    {N : Nat} [NeZero N] (i : Fin N) :
    finCompletionBaseStep i = i + 1 :=
  rfl

theorem finCompletionBaseStep_rank_closed
    {N : Nat} [NeZero N] (i : Fin N) :
    (ZMod.finEquiv N).toEquiv (finCompletionBaseStep i) =
      (ZMod.finEquiv N).toEquiv i + 1 :=
  finCompletionBaseStep_rank i

theorem finCompletionCarryCertificate_eq_pointCarry_closed
    {N n m : Nat} (C : FinCompletionCarryCertificate N n m) :
    completionCarry C.coordRead (cyclicCompletionRow C.shift) C.tail =
      pointCarry C.crossing C.epsilon :=
  finCompletionCarryCertificate_eq_pointCarry C

theorem finCompletionCarryCertificate_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionCarryCertificate N n m)
    (hepsilon : IsUnit C.epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry C.coordRead (cyclicCompletionRow C.shift)
          C.tail)) :=
  finCompletionCarryCertificate_singleCycle C hepsilon

theorem finCompletionTargetAvoids_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N} :
    finCompletionTargetAvoids target shift tail crossing =
      (∀ i : Fin N, i ≠ crossing →
        completionTargetAvoids target shift (tail i)) :=
  rfl

theorem finCompletionTailAvoidsTarget_closed
    {N n : Nat} {target : ZMod n}
    {tail : Fin N → ZMod n} :
    finCompletionTailAvoidsTarget target tail =
      (∀ i : Fin N, tail i ≠ target) :=
  rfl

theorem finCompletionOffCrossingTailAvoidsTarget_closed
    {N n : Nat} {target : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N} :
    finCompletionOffCrossingTailAvoidsTarget
        target tail crossing =
      (∀ i : Fin N, i ≠ crossing → tail i ≠ target) :=
  rfl

theorem finCompletionTailAvoidsTarget_of_offCrossing_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing) :
    finCompletionTailAvoidsTarget target tail :=
  finCompletionTailAvoidsTarget_of_offCrossing
    hshift hcrossTail hoffTail

theorem finCompletionRowTargetHitsOnlyAtCrossing_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N} :
    finCompletionRowTargetHitsOnlyAtCrossing
        target shift tail crossing =
      (∀ i : Fin N, cyclicCompletionRow shift (tail i) = target →
        i = crossing) :=
  rfl

theorem finCompletionTargetProfile_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N} :
    finCompletionTargetProfile target shift tail crossing =
      (finCompletionTailAvoidsTarget target tail ∧
        finCompletionRowTargetHitsOnlyAtCrossing
          target shift tail crossing) :=
  rfl

theorem finCompletionRowTargetHitsOnlyAtCrossing_of_injective_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailInj : Function.Injective tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionRowTargetHitsOnlyAtCrossing
      target shift tail crossing :=
  finCompletionRowTargetHitsOnlyAtCrossing_of_injective_tail
    htailInj hcrossTail

theorem finCompletionTargetProfile_of_injective_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetProfile target shift tail crossing :=
  finCompletionTargetProfile_of_injective_tail
    htailAvoids htailInj hcrossTail

theorem finCompletionTargetAvoids_of_injective_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_injective_tail
    htailAvoids htailInj hcrossTail

theorem finCompletionTargetAvoids_of_targetProfile_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_targetProfile hprofile

theorem finCompletionCarryCertificateOfTargetAvoidance_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (havoid : finCompletionTargetAvoids target shift tail crossing) :
    @finCompletionCarryCertificateOfTargetAvoidance
        N n m target shift tail crossing hshift hcrossTail havoid =
      @finCompletionCarryCertificateOfTargetIndicator
        N n m target shift tail crossing hshift hcrossTail
        (fun i hi => (havoid i hi).1)
        (fun i hi => (havoid i hi).2) :=
  rfl

theorem finCompletionCarryCertificateOfTargetProfile_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    @finCompletionCarryCertificateOfTargetProfile
        N n m target shift tail crossing hshift hcrossTail hprofile =
      @finCompletionCarryCertificateOfTargetAvoidance
        N n m target shift tail crossing hshift hcrossTail
        (finCompletionTargetAvoids_of_targetProfile hprofile) :=
  rfl

theorem finCompletionCarryCertificateOfInjectiveTail_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail) :
    @finCompletionCarryCertificateOfInjectiveTail
        N n m target shift tail crossing hshift hcrossTail
        htailAvoids htailInj =
      @finCompletionCarryCertificateOfTargetProfile
        N n m target shift tail crossing hshift hcrossTail
        (finCompletionTargetProfile_of_injective_tail
          htailAvoids htailInj hcrossTail) :=
  rfl

theorem finCompletionCarryCertificateOfTargetAvoidance_eq_pointCarry_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (havoid : finCompletionTargetAvoids target shift tail crossing) :
    completionCarry (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfTargetAvoidance_eq_pointCarry
    target shift tail crossing hshift hcrossTail havoid

theorem finCompletionCarryCertificateOfTargetAvoidance_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (havoid : finCompletionTargetAvoids target shift tail crossing) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfTargetAvoidance_singleCycle
    target shift tail crossing hshift hcrossTail havoid

theorem finCompletionCarryCertificateOfTargetProfile_eq_pointCarry_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    completionCarry (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfTargetProfile_eq_pointCarry
    target shift tail crossing hshift hcrossTail hprofile

theorem finCompletionCarryCertificateOfTargetProfile_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfTargetProfile_singleCycle
    target shift tail crossing hshift hcrossTail hprofile

theorem finCompletionCarryCertificateOfInjectiveTail_eq_pointCarry_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail) :
    completionCarry (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfInjectiveTail_eq_pointCarry
    target shift tail crossing hshift hcrossTail htailAvoids htailInj

theorem finCompletionCarryCertificateOfInjectiveTail_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfInjectiveTail_singleCycle
    target shift tail crossing hshift hcrossTail htailAvoids htailInj

theorem finCompletionInjectiveTailCertificate_targetProfile_closed
    {N n : Nat} (C : FinCompletionInjectiveTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionInjectiveTailCertificate_targetProfile C

theorem finCompletionInjectiveTailCertificate_targetAvoids_closed
    {N n : Nat} (C : FinCompletionInjectiveTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionInjectiveTailCertificate_targetAvoids C

theorem finCompletionInjectiveTailCertificate_eq_pointCarry_closed
    {N n m : Nat} (C : FinCompletionInjectiveTailCertificate N n) :
    completionCarry (@targetIndicatorCoordRead n m C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionInjectiveTailCertificate_eq_pointCarry C

theorem finCompletionInjectiveTailCertificate_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionInjectiveTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionInjectiveTailCertificate_singleCycle C

theorem finCompletionTailPairwiseSeparated_closed
    {N n : Nat} {tail : Fin N → ZMod n} :
    finCompletionTailPairwiseSeparated tail =
      (∀ i j : Fin N, i ≠ j → tail i ≠ tail j) :=
  rfl

theorem finCompletionTailPairwiseSeparated_injective_closed
    {N n : Nat} {tail : Fin N → ZMod n}
    (hsep : finCompletionTailPairwiseSeparated tail) :
    Function.Injective tail :=
  finCompletionTailPairwiseSeparated_injective hsep

theorem mem_finCompletionTailList_closed
    {N n : Nat} {tail : Fin N → ZMod n} {coord : ZMod n} :
    coord ∈ finCompletionTailList tail ↔
      ∃ i : Fin N, tail i = coord :=
  mem_finCompletionTailList

theorem mem_finCompletionOffCrossingTailList_closed
    {N n : Nat} {tail : Fin N → ZMod n}
    {crossing : Fin N} {coord : ZMod n} :
    coord ∈ finCompletionOffCrossingTailList tail crossing ↔
      ∃ i : Fin N, i ≠ crossing ∧ tail i = coord :=
  mem_finCompletionOffCrossingTailList

theorem finCompletionTailAvoidsTarget_of_target_not_mem_tailList_closed
    {N n : Nat} {target : ZMod n} {tail : Fin N → ZMod n}
    (hnot : target ∉ finCompletionTailList tail) :
    finCompletionTailAvoidsTarget target tail :=
  finCompletionTailAvoidsTarget_of_target_not_mem_tailList hnot

theorem finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList_closed
    {N n : Nat} {target : ZMod n} {tail : Fin N → ZMod n}
    {crossing : Fin N}
    (hnot : target ∉ finCompletionOffCrossingTailList tail crossing) :
    finCompletionOffCrossingTailAvoidsTarget target tail crossing :=
  finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
    hnot

theorem finCompletionTargetProfile_of_separated_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetProfile target shift tail crossing :=
  finCompletionTargetProfile_of_separated_tail
    htailAvoids htailSep hcrossTail

theorem finCompletionTargetAvoids_of_separated_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_separated_tail
    htailAvoids htailSep hcrossTail

theorem finCompletionCarryCertificateOfSeparatedTail_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    @finCompletionCarryCertificateOfSeparatedTail
        N n m target shift tail crossing hshift hcrossTail
        htailAvoids htailSep =
      @finCompletionCarryCertificateOfInjectiveTail
        N n m target shift tail crossing hshift hcrossTail
        htailAvoids
        (finCompletionTailPairwiseSeparated_injective htailSep) :=
  rfl

theorem finCompletionCarryCertificateOfSeparatedTail_eq_pointCarry_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    completionCarry (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfSeparatedTail_eq_pointCarry
    target shift tail crossing hshift hcrossTail htailAvoids
    htailSep

theorem finCompletionCarryCertificateOfSeparatedTail_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfSeparatedTail_singleCycle
    target shift tail crossing hshift hcrossTail htailAvoids
    htailSep

theorem finCompletionTargetProfile_of_offCrossing_separated_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetProfile target shift tail crossing :=
  finCompletionTargetProfile_of_offCrossing_separated_tail
    hshift hcrossTail hoffTail htailSep

theorem finCompletionTargetAvoids_of_offCrossing_separated_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_offCrossing_separated_tail
    hshift hcrossTail hoffTail htailSep

theorem finCompletionCarryCertificateOfOffCrossingSeparatedTail_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    @finCompletionCarryCertificateOfOffCrossingSeparatedTail
        N n m target shift tail crossing hshift hcrossTail
        hoffTail htailSep =
      @finCompletionCarryCertificateOfSeparatedTail
        N n m target shift tail crossing hshift hcrossTail
        (finCompletionTailAvoidsTarget_of_offCrossing
          hshift hcrossTail hoffTail)
        htailSep :=
  rfl

theorem finCompletionCarryCertificateOfOffCrossingSeparatedTail_eq_pointCarry_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    completionCarry (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfOffCrossingSeparatedTail_eq_pointCarry
    target shift tail crossing hshift hcrossTail hoffTail htailSep

theorem finCompletionCarryCertificateOfOffCrossingSeparatedTail_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfOffCrossingSeparatedTail_singleCycle
    target shift tail crossing hshift hcrossTail hoffTail htailSep

theorem finCompletionTargetProfile_of_offCrossing_tailList_separated_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetProfile target shift tail crossing :=
  finCompletionTargetProfile_of_offCrossing_tailList_separated_tail
    hshift hcrossTail hnot htailSep

theorem finCompletionTargetAvoids_of_offCrossing_tailList_separated_tail_closed
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_offCrossing_tailList_separated_tail
    hshift hcrossTail hnot htailSep

theorem finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_eq_pointCarry_closed
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    completionCarry (@targetIndicatorCoordRead n m target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_eq_pointCarry
    target shift tail crossing hshift hcrossTail hnot htailSep

theorem finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_singleCycle
    target shift tail crossing hshift hcrossTail hnot htailSep

theorem finCompletionSeparatedTailCertificate_tailInjective_closed
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    Function.Injective C.tail :=
  finCompletionSeparatedTailCertificate_tailInjective C

theorem finCompletionSeparatedTailCertificate_targetProfile_closed
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionSeparatedTailCertificate_targetProfile C

theorem finCompletionSeparatedTailCertificate_targetAvoids_closed
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionSeparatedTailCertificate_targetAvoids C

theorem finCompletionSeparatedTailCertificate_eq_pointCarry_closed
    {N n m : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    completionCarry (@targetIndicatorCoordRead n m C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionSeparatedTailCertificate_eq_pointCarry C

theorem finCompletionSeparatedTailCertificate_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionSeparatedTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionSeparatedTailCertificate_singleCycle C

theorem finCompletionOffCrossingSeparatedTailCertificate_tailAvoidsTarget_closed
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    finCompletionTailAvoidsTarget C.target C.tail :=
  finCompletionOffCrossingSeparatedTailCertificate_tailAvoidsTarget C

theorem finCompletionOffCrossingSeparatedTailCertificate_targetProfile_closed
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionOffCrossingSeparatedTailCertificate_targetProfile C

theorem finCompletionOffCrossingSeparatedTailCertificate_targetAvoids_closed
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionOffCrossingSeparatedTailCertificate_targetAvoids C

theorem finCompletionOffCrossingSeparatedTailCertificate_eq_pointCarry_closed
    {N n m : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    completionCarry (@targetIndicatorCoordRead n m C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionOffCrossingSeparatedTailCertificate_eq_pointCarry C

theorem finCompletionOffCrossingSeparatedTailCertificate_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionOffCrossingSeparatedTailCertificate_singleCycle C

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_offCrossingTailAvoidsTarget_closed
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    finCompletionOffCrossingTailAvoidsTarget
      C.target C.tail C.crossing :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_offCrossingTailAvoidsTarget
    C

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_targetProfile_closed
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_targetProfile C

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_targetAvoids_closed
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_targetAvoids C

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_eq_pointCarry_closed
    {N n m : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    completionCarry (@targetIndicatorCoordRead n m C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_eq_pointCarry C

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_singleCycle_closed
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (@targetIndicatorCoordRead n m C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_singleCycle C

theorem endpointB4FirstCompletionTarget_closed :
    endpointB4FirstCompletionTarget = (8 : ZMod 9) :=
  rfl

theorem endpointB4FirstCompletionShift_closed :
    endpointB4FirstCompletionShift = (1 : ZMod 9) :=
  rfl

theorem endpointB4FirstCompletionTail_closed :
    endpointB4FirstCompletionTail = (7 : ZMod 9) :=
  rfl

theorem endpointB4FirstCompletionCoordRead_closed
    {m : Nat} (coord : ZMod 9) :
    @endpointB4FirstCompletionCoordRead m coord =
      targetIndicatorCoordRead endpointB4FirstCompletionTarget coord :=
  rfl

theorem endpointB4FirstCompletion_tail_closed :
    cyclicCompletionTail endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift =
        endpointB4FirstCompletionTail :=
  endpointB4FirstCompletion_tail

theorem endpointB4FirstCompletion_row_closed :
    cyclicCompletionRow endpointB4FirstCompletionShift
      endpointB4FirstCompletionTail =
        endpointB4FirstCompletionTarget :=
  endpointB4FirstCompletion_row

theorem endpointB4FirstCompletion_shift_ne_zero_closed :
    endpointB4FirstCompletionShift ≠ (0 : ZMod 9) :=
  endpointB4FirstCompletion_shift_ne_zero

theorem endpointB4FirstCompletionCoordRead_target_closed
    {m : Nat} :
    @endpointB4FirstCompletionCoordRead m
      endpointB4FirstCompletionTarget = 1 :=
  endpointB4FirstCompletionCoordRead_target

theorem endpointB4FirstCompletionCoordRead_tail_closed
    {m : Nat} :
    @endpointB4FirstCompletionCoordRead m
      endpointB4FirstCompletionTail = 0 :=
  endpointB4FirstCompletionCoordRead_tail

theorem endpointB4FirstCompletion_tail_ne_target_closed :
    endpointB4FirstCompletionTail ≠
      endpointB4FirstCompletionTarget :=
  endpointB4FirstCompletion_tail_ne_target

theorem endpointB4FirstCompletionTailAvoidsTarget_closed :
    finCompletionTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) :=
  endpointB4FirstCompletionTailAvoidsTarget

theorem endpointB4FirstCompletionRowTargetHitsOnlyAtCrossing_closed :
    finCompletionRowTargetHitsOnlyAtCrossing
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionRowTargetHitsOnlyAtCrossing

theorem endpointB4FirstCompletionTail_pairwiseSeparated_closed :
    finCompletionTailPairwiseSeparated
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) :=
  endpointB4FirstCompletionTail_pairwiseSeparated

theorem endpointB4FirstCompletionOffCrossingTailAvoidsTarget_closed :
    finCompletionOffCrossingTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionOffCrossingTailAvoidsTarget

theorem endpointB4FirstCompletionTailAvoidsTarget_fromOffCrossing_closed :
    finCompletionTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) :=
  endpointB4FirstCompletionTailAvoidsTarget_fromOffCrossing

theorem endpointB4FirstCompletionTail_injective_closed :
    Function.Injective
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) :=
  endpointB4FirstCompletionTail_injective

theorem endpointB4FirstCompletionTargetProfile_closed :
    finCompletionTargetProfile
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionTargetProfile

theorem endpointB4FirstCompletionTargetAvoids_closed :
    finCompletionTargetAvoids
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionTargetAvoids

theorem endpointB4FirstCompletionOffCrossingTarget_not_mem_tailList_closed :
    endpointB4FirstCompletionTarget ∉
      finCompletionOffCrossingTailList
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionOffCrossingTarget_not_mem_tailList

theorem endpointB4FirstCompletionOffCrossingTailListAvoidsTarget_closed :
    finCompletionOffCrossingTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionOffCrossingTailListAvoidsTarget

theorem endpointB4FirstCompletionOffCrossingTailListTargetProfile_closed :
    finCompletionTargetProfile
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionOffCrossingTailListTargetProfile

theorem endpointB4FirstCompletionOffCrossingTailListTargetAvoids_closed :
    finCompletionTargetAvoids
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  endpointB4FirstCompletionOffCrossingTailListTargetAvoids

theorem endpointB4FirstCompletionOffCrossingOnePointCertificate_closed
    (m : Nat) :
    endpointB4FirstCompletionOffCrossingOnePointCertificate m =
      FinCompletionOffCrossingSeparatedTailCertificate.toCarryCertificate
        endpointB4FirstCompletionOffCrossingSeparatedTailCertificate m :=
  rfl

theorem endpointB4FirstCompletionOffCrossingTailListOnePointCertificate_fromTailList_closed
    (m : Nat) :
    endpointB4FirstCompletionOffCrossingTailListOnePointCertificate m =
      FinCompletionOffCrossingTailListSeparatedTailCertificate.toCarryCertificate
        endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate m :=
  endpointB4FirstCompletionOffCrossingTailListOnePointCertificate_fromTailList
    m

theorem endpointB4FirstCompletionTailListOnePointCertificate_eq_pointCarry_closed
    {m : Nat} :
    completionCarry
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).coordRead
        (cyclicCompletionRow
          (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
            m).shift)
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).tail =
      pointCarry
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).crossing
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).epsilon :=
  endpointB4FirstCompletionTailListOnePointCertificate_eq_pointCarry

theorem endpointB4FirstCompletionTailListOnePointCertificate_singleCycle_closed
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
            m).coordRead
          (cyclicCompletionRow
            (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
              m).shift)
          (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
            m).tail)) :=
  endpointB4FirstCompletionTailListOnePointCertificate_singleCycle

theorem endpointB4FirstCompletionOffCrossingOnePointCertificate_fromTail_closed
    (m : Nat) :
    endpointB4FirstCompletionOffCrossingOnePointCertificate m =
      FinCompletionOffCrossingSeparatedTailCertificate.toCarryCertificate
        endpointB4FirstCompletionOffCrossingSeparatedTailCertificate m :=
  endpointB4FirstCompletionOffCrossingOnePointCertificate_fromTail m

theorem endpointB4FirstCompletionOffCrossingSeparatedTail_eq_pointCarry_closed
    {m : Nat} :
    completionCarry
        (@targetIndicatorCoordRead 9 m
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  endpointB4FirstCompletionOffCrossingSeparatedTail_eq_pointCarry

theorem endpointB4FirstCompletionOffCrossingSeparatedTail_singleCycle_closed
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (@targetIndicatorCoordRead 9 m
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  endpointB4FirstCompletionOffCrossingSeparatedTail_singleCycle

theorem endpointB4FirstCompletionOffCrossingTailListSeparatedTail_eq_pointCarry_closed
    {m : Nat} :
    completionCarry
        (@targetIndicatorCoordRead 9 m
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  endpointB4FirstCompletionOffCrossingTailListSeparatedTail_eq_pointCarry

theorem endpointB4FirstCompletionOffCrossingTailListSeparatedTail_singleCycle_closed
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (@targetIndicatorCoordRead 9 m
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  endpointB4FirstCompletionOffCrossingTailListSeparatedTail_singleCycle

theorem endpointB4FirstCompletionInjectiveTailCertificate_eq_pointCarry_closed
    {m : Nat} :
    completionCarry
        (@targetIndicatorCoordRead 9 m
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  endpointB4FirstCompletionInjectiveTailCertificate_eq_pointCarry

theorem endpointB4FirstCompletionInjectiveTailCertificate_singleCycle_closed
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (@targetIndicatorCoordRead 9 m
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  endpointB4FirstCompletionInjectiveTailCertificate_singleCycle

theorem endpointB4FirstCompletionSeparatedTailCertificate_eq_pointCarry_closed
    {m : Nat} :
    completionCarry
        (@targetIndicatorCoordRead 9 m
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  endpointB4FirstCompletionSeparatedTailCertificate_eq_pointCarry

theorem endpointB4FirstCompletionSeparatedTailCertificate_singleCycle_closed
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (@targetIndicatorCoordRead 9 m
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  endpointB4FirstCompletionSeparatedTailCertificate_singleCycle

theorem endpointB4FirstCompletionOnePointCertificate_fromSeparatedTail_closed
    (m : Nat) :
    endpointB4FirstCompletionOnePointCertificate m =
      FinCompletionSeparatedTailCertificate.toCarryCertificate
        endpointB4FirstCompletionSeparatedTailCertificate m :=
  endpointB4FirstCompletionOnePointCertificate_fromSeparatedTail m

theorem endpointB4FirstCompletionOnePointCertificate_eq_pointCarry_closed
    {m : Nat} :
    completionCarry
        (endpointB4FirstCompletionOnePointCertificate m).coordRead
        (cyclicCompletionRow
          (endpointB4FirstCompletionOnePointCertificate m).shift)
        (endpointB4FirstCompletionOnePointCertificate m).tail =
      pointCarry
        (endpointB4FirstCompletionOnePointCertificate m).crossing
        (endpointB4FirstCompletionOnePointCertificate m).epsilon :=
  endpointB4FirstCompletionOnePointCertificate_eq_pointCarry

theorem endpointB4FirstCompletionOnePointCertificate_singleCycle_closed
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (endpointB4FirstCompletionOnePointCertificate m).coordRead
          (cyclicCompletionRow
            (endpointB4FirstCompletionOnePointCertificate m).shift)
          (endpointB4FirstCompletionOnePointCertificate m).tail)) :=
  endpointB4FirstCompletionOnePointCertificate_singleCycle

theorem planeSpan_of_lineSpan_closed
    {m r : Nat} (e g x : Vec m r)
    (hxLine : lineSpan e x) :
    planeSpan e g x :=
  planeSpan_of_lineSpan e g x hxLine

theorem lineCoset_refl_closed
    {m r : Nat} (e x : Vec m r) :
    lineCoset e x x :=
  lineCoset_refl e x

theorem lineCoset_symm_closed
    {m r : Nat} (e x y : Vec m r)
    (hxy : lineCoset e x y) :
    lineCoset e y x :=
  lineCoset_symm e x y hxy

theorem lineCoset_trans_closed
    {m r : Nat} (e x y z : Vec m r)
    (hxy : lineCoset e x y) (hyz : lineCoset e y z) :
    lineCoset e x z :=
  lineCoset_trans e x y z hxy hyz

theorem lineCoset_zero_iff_lineSpan_closed
    {m r : Nat} (e x : Vec m r) :
    lineCoset e (0 : Vec m r) x ↔ lineSpan e x :=
  lineCoset_zero_iff_lineSpan e x

theorem lineCoset_zero_of_lineSpan_closed
    {m r : Nat} (e x : Vec m r)
    (hxLine : lineSpan e x) :
    lineCoset e (0 : Vec m r) x :=
  lineCoset_zero_of_lineSpan e x hxLine

theorem planeLineQuotient_mk_eq_of_lineCoset_closed
    {m r : Nat} (e g x y : Vec m r)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y)
    (hxy : lineCoset e x y) :
    planeLineQuotientMk e g x hxPlane =
      planeLineQuotientMk e g y hyPlane :=
  planeLineQuotient_mk_eq_of_lineCoset e g x y hxPlane hyPlane hxy

theorem planeLineQuotient_eq_zero_of_lineSpan_closed
    {m r : Nat} (e g x : Vec m r)
    (hxPlane : planeSpan e g x) (hxLine : lineSpan e x) :
    planeLineQuotientMk e g x hxPlane =
      planeLineQuotientZero e g :=
  planeLineQuotient_eq_zero_of_lineSpan e g x hxPlane hxLine

theorem lineSpan_of_lineCoset_zero_closed
    {m r : Nat} (e x : Vec m r)
    (hxCoset : lineCoset e (0 : Vec m r) x) :
    lineSpan e x :=
  lineSpan_of_lineCoset_zero e x hxCoset

theorem lineSpan_of_lineCoset_of_lineSpan_closed
    {m r : Nat} (e x y : Vec m r)
    (hxLine : lineSpan e x) (hxy : lineCoset e x y) :
    lineSpan e y :=
  lineSpan_of_lineCoset_of_lineSpan e x y hxLine hxy

theorem planeSpan_of_lineCoset_of_planeSpan_closed
    {m r : Nat} (e g x y : Vec m r)
    (hxPlane : planeSpan e g x) (hxy : lineCoset e x y) :
    planeSpan e g y :=
  planeSpan_of_lineCoset_of_planeSpan e g x y hxPlane hxy

theorem theta_eq_zero_of_lineSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxLine : lineSpan e x) :
    theta x = 0 :=
  theta_eq_zero_of_lineSpan theta e g x hThetaPlane hxLine

theorem lineSpan_of_planeSpan_of_theta_eq_zero_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x)
    (hThetaZero : theta x = 0) :
    lineSpan e x :=
  lineSpan_of_planeSpan_of_theta_eq_zero theta e g x
    hThetaPlane hxPlane hThetaZero

theorem theta_eq_of_lineCoset_of_planeSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hxy : lineCoset e x y) :
    theta y = theta x :=
  theta_eq_of_lineCoset_of_planeSpan theta e g x y
    hThetaPlane hxPlane hxy

theorem planeLineQuotientTheta_mk_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    planeLineQuotientTheta theta e g hThetaPlane
      (planeLineQuotientMk e g x hxPlane) = theta x :=
  planeLineQuotientTheta_mk theta e g x hThetaPlane hxPlane

theorem planeLineQuotientTheta_zero_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    planeLineQuotientTheta theta e g hThetaPlane
      (planeLineQuotientZero e g) = 0 :=
  planeLineQuotientTheta_zero theta e g hThetaPlane

theorem theta_eq_zero_of_lineCoset_of_lineSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxLine : lineSpan e x) (hxy : lineCoset e x y) :
    theta y = 0 :=
  theta_eq_zero_of_lineCoset_of_lineSpan theta e g x y
    hThetaPlane hxLine hxy

theorem lineCoset_of_planeSpan_of_theta_eq_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y)
    (hThetaEq : theta y = theta x) :
    lineCoset e x y :=
  lineCoset_of_planeSpan_of_theta_eq theta e g x y
    hThetaPlane hxPlane hyPlane hThetaEq

theorem lineCoset_iff_theta_eq_of_planeSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y) :
    lineCoset e x y ↔ theta y = theta x :=
  lineCoset_iff_theta_eq_of_planeSpan theta e g x y
    hThetaPlane hxPlane hyPlane

theorem planeLineQuotientTheta_eq_iff_lineCoset_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x y : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) (hyPlane : planeSpan e g y) :
    planeLineQuotientTheta theta e g hThetaPlane
        (planeLineQuotientMk e g x hxPlane) =
      planeLineQuotientTheta theta e g hThetaPlane
        (planeLineQuotientMk e g y hyPlane) ↔
      lineCoset e x y :=
  planeLineQuotientTheta_eq_iff_lineCoset theta e g x y
    hThetaPlane hxPlane hyPlane

theorem planeSpan_lineCoset_subset_thetaFiber_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    {y : Vec m r | planeSpan e g y ∧ lineCoset e x y} ⊆
      {y : Vec m r | planeSpan e g y ∧ theta y = theta x} :=
  planeSpan_lineCoset_subset_thetaFiber theta e g x
    hThetaPlane hxPlane

theorem planeSpan_thetaFiber_subset_lineCoset_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    {y : Vec m r | planeSpan e g y ∧ theta y = theta x} ⊆
      {y : Vec m r | planeSpan e g y ∧ lineCoset e x y} :=
  planeSpan_thetaFiber_subset_lineCoset theta e g x
    hThetaPlane hxPlane

theorem planeSpan_lineCoset_set_eq_thetaFiber_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    {y : Vec m r | planeSpan e g y ∧ lineCoset e x y} =
      {y : Vec m r | planeSpan e g y ∧ theta y = theta x} :=
  planeSpan_lineCoset_set_eq_thetaFiber theta e g x
    hThetaPlane hxPlane

theorem lineSpan_iff_theta_eq_zero_of_planeSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    lineSpan e x ↔ theta x = 0 :=
  lineSpan_iff_theta_eq_zero_of_planeSpan theta e g x
    hThetaPlane hxPlane

theorem planeLineQuotientTheta_eq_zero_iff_lineSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hxPlane : planeSpan e g x) :
    planeLineQuotientTheta theta e g hThetaPlane
        (planeLineQuotientMk e g x hxPlane) = 0 ↔
      lineSpan e x :=
  planeLineQuotientTheta_eq_zero_iff_lineSpan theta e g x
    hThetaPlane hxPlane

theorem lineSpan_iff_planeSpan_and_theta_eq_zero_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    lineSpan e x ↔ planeSpan e g x ∧ theta x = 0 :=
  lineSpan_iff_planeSpan_and_theta_eq_zero theta e g x hThetaPlane

theorem lineSpan_subset_planeSpan_thetaKernel_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    {x : Vec m r | lineSpan e x} ⊆
      {x : Vec m r | planeSpan e g x ∧ theta x = 0} :=
  lineSpan_subset_planeSpan_thetaKernel theta e g hThetaPlane

theorem planeSpan_thetaKernel_subset_lineSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    {x : Vec m r | planeSpan e g x ∧ theta x = 0} ⊆
      {x : Vec m r | lineSpan e x} :=
  planeSpan_thetaKernel_subset_lineSpan theta e g hThetaPlane

theorem lineSpan_set_eq_planeSpan_thetaKernel_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b) :
    {x : Vec m r | lineSpan e x} =
      {x : Vec m r | planeSpan e g x ∧ theta x = 0} :=
  lineSpan_set_eq_planeSpan_thetaKernel theta e g hThetaPlane

theorem theta_eq_zero_of_translatedLineSet_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e x : Vec m r)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxTranslatedLine : translatedLineSet H e x) :
    theta x = 0 :=
  theta_eq_zero_of_translatedLineSet theta H e x
    hThetaTranslatedLine hxTranslatedLine

theorem translatedLineSet_subset_thetaKernel_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e : Vec m r)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0) :
    {x : Vec m r | translatedLineSet H e x} ⊆
      {x : Vec m r | theta x = 0} :=
  translatedLineSet_subset_thetaKernel theta H e hThetaTranslatedLine

theorem translatedTwoLineSet_closed
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 x : Vec m r) :
    translatedTwoLineSet H e0 e1 x =
      (∃ h : Vec m r, ∃ a b : ZMod m,
        H h ∧ x = fun i => h i + a * e0 i + b * e1 i) :=
  rfl

theorem triangularPlaneGenerator_closed
    {m r : Nat} (e0 g1 : Vec m r) (i : Fin r) :
    triangularPlaneGenerator e0 g1 i = e0 i + g1 i :=
  rfl

theorem projectionKernelCriterion_coordinate_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    lineSpan e x :=
  projectionKernelCriterion_coordinate theta H e g x
    hThetaPlane hThetaTranslatedLine hxPlane hxTranslatedLine

theorem planeSpan_translatedLineSet_subset_lineSpan_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0) :
    {x : Vec m r | planeSpan e g x ∧ translatedLineSet H e x} ⊆
      {x : Vec m r | lineSpan e x} :=
  planeSpan_translatedLineSet_subset_lineSpan theta H e g
    hThetaPlane hThetaTranslatedLine

theorem projectionKernelCriterion_set_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0) :
    {x : Vec m r | planeSpan e g x ∧ translatedLineSet H e x} ⊆
      {x : Vec m r | lineSpan e x} :=
  projectionKernelCriterion_set theta H e g
    hThetaPlane hThetaTranslatedLine

theorem projectionKernelCriterion_lineCosetZero_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    lineCoset e (0 : Vec m r) x :=
  projectionKernelCriterion_lineCosetZero theta H e g x
    hThetaPlane hThetaTranslatedLine hxPlane hxTranslatedLine

theorem projectionKernelCriterion_planeLineQuotientZero_closed
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    planeLineQuotientMk e g x hxPlane =
      planeLineQuotientZero e g :=
  projectionKernelCriterion_planeLineQuotientZero theta H e g x
    hThetaPlane hThetaTranslatedLine hxPlane hxTranslatedLine

theorem triangularTwoLeafProjectionKernel_coordinate_closed
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    lineSpan e1 x :=
  triangularTwoLeafProjectionKernel_coordinate H e0 e1 g1 x
    hkill hxPlane hxTranslated

theorem triangularTwoLeafProjectionKernel_set_closed
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0) :
    {x : Vec m r |
      planeSpan e1 (triangularPlaneGenerator e0 g1) x ∧
        translatedTwoLineSet H e0 e1 x} ⊆
      {x : Vec m r | lineSpan e1 x} :=
  triangularTwoLeafProjectionKernel_set H e0 e1 g1 hkill

theorem triangularTwoLeafProjectionKernel_lineCosetZero_closed
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    lineCoset e1 (0 : Vec m r) x :=
  triangularTwoLeafProjectionKernel_lineCosetZero H e0 e1 g1 x
    hkill hxPlane hxTranslated

theorem triangularTwoLeafProjectionKernel_planeLineQuotientZero_closed
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    planeLineQuotientMk e1 (triangularPlaneGenerator e0 g1)
        x hxPlane =
      planeLineQuotientZero e1 (triangularPlaneGenerator e0 g1) :=
  triangularTwoLeafProjectionKernel_planeLineQuotientZero
    H e0 e1 g1 x hkill hxPlane hxTranslated

theorem mem_of_nonzero_of_vanishesOutside_closed
    {α Value : Type*} [Zero Value]
    (theta : α → Value) (allowed : Set α)
    (hzero : VanishesOutside theta allowed) {x : α}
    (hne : theta x ≠ 0) :
    x ∈ allowed :=
  mem_of_nonzero_of_vanishesOutside theta allowed hzero hne

theorem theta_eq_zero_of_not_mem_of_vanishesOutside_closed
    {α Value : Type*} [Zero Value]
    (theta : α → Value) (allowed : Set α)
    (hzero : VanishesOutside theta allowed) {x : α}
    (hx : x ∉ allowed) :
    theta x = 0 :=
  theta_eq_zero_of_not_mem_of_vanishesOutside theta allowed hzero hx

theorem theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (allowedCenters : Set Center)
    (hzero : VanishesOutsideGuide theta center allowedCenters)
    {row : Row} (hcenter : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide theta center
    allowedCenters hzero hcenter

theorem theta_eq_zero_of_center_not_mem_guideList_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (centers : List Center)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hcenter : center row ∉ centers) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_guideList theta center
    centers hzero hcenter

theorem vanishesOutside_of_subset_closed
    {α Value : Type*} [Zero Value]
    (theta : α → Value) {actual allowed : Set α}
    (hsubset : actual ⊆ allowed)
    (hzero : VanishesOutside theta actual) :
    VanishesOutside theta allowed :=
  vanishesOutside_of_subset theta hsubset hzero

theorem theta_eq_zero_of_not_mem_of_vanishesOutside_subset_closed
    {α Value : Type*} [Zero Value]
    (theta : α → Value) {actual allowed : Set α}
    (hsubset : actual ⊆ allowed)
    (hzero : VanishesOutside theta actual) {x : α}
    (hxAllowed : x ∉ allowed) :
    theta x = 0 :=
  theta_eq_zero_of_not_mem_of_vanishesOutside_subset theta
    hsubset hzero hxAllowed

theorem vanishesOutsideGuide_of_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters allowedCenters : Set Center}
    (hsubset : actualCenters ⊆ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters) :
    VanishesOutsideGuide theta center allowedCenters :=
  vanishesOutsideGuide_of_subset theta center hsubset hzero

theorem theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters allowedCenters : Set Center}
    (hsubset : actualCenters ⊆ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hcenter : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_vanishesOutsideGuide_subset
    theta center hsubset hzero hcenter

theorem vanishesOutsideGuide_of_list_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center} {allowedCenters : Set Center}
    (hsubset : ∀ c : Center, c ∈ centers → c ∈ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers) :
    VanishesOutsideGuide theta center allowedCenters :=
  vanishesOutsideGuide_of_list_subset theta center hsubset hzero

theorem theta_eq_zero_of_center_not_mem_of_guideList_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center} {allowedCenters : Set Center}
    (hsubset : ∀ c : Center, c ∈ centers → c ∈ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hcenter : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_of_guideList_subset theta center
    hsubset hzero hcenter

theorem guideLocalityOfNonzero_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (allowedCenters : Set Center) {row : Row}
    (hzero : VanishesOutsideGuide theta center allowedCenters)
    (hne : theta row ≠ 0) :
    center row ∈ allowedCenters :=
  guideLocalityOfNonzero theta center allowedCenters hzero hne

theorem guideLocalityOfNonzero_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters allowedCenters : Set Center}
    (hsubset : actualCenters ⊆ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    center row ∈ allowedCenters :=
  guideLocalityOfNonzero_subset theta center hsubset hzero hne

theorem guideLocalityOfNonzero_list_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (centers : List Center)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hne : theta row ≠ 0) :
    center row ∈ centers :=
  guideLocalityOfNonzero_list theta center centers hzero hne

theorem guideLocalityOfNonzero_list_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center} {allowedCenters : Set Center}
    (hsubset : ∀ c : Center, c ∈ centers → c ∈ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hne : theta row ≠ 0) :
    center row ∈ allowedCenters :=
  guideLocalityOfNonzero_list_subset theta center hsubset hzero hne

theorem mem_tripleGuideList_iff_closed {Center : Type*}
    (left middle right c : Center) :
    c ∈ TripleGuideList left middle right ↔
      c = left ∨ c = middle ∨ c = right :=
  mem_tripleGuideList_iff left middle right c

theorem guideCenterListSet_tripleGuideList_closed {Center : Type*}
    (left middle right : Center) :
    GuideCenterListSet (TripleGuideList left middle right) =
      TripleGuideSet left middle right :=
  guideCenterListSet_tripleGuideList left middle right

theorem mem_additiveTripleGuideList_iff_closed
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta c : Center) :
    c ∈ AdditiveTripleGuideList rho delta ↔
      c = rho - delta ∨ c = rho ∨ c = rho + delta :=
  mem_additiveTripleGuideList_iff rho delta c

theorem guideCenterListSet_additiveTripleGuideList_closed
    {Center : Type*} [Sub Center] [Add Center] (rho delta : Center) :
    GuideCenterListSet (AdditiveTripleGuideList rho delta) =
      AdditiveTripleGuideSet rho delta :=
  guideCenterListSet_additiveTripleGuideList rho delta

theorem vanishesOutsideGuide_tripleGuideList_iff_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) :
    VanishesOutsideGuideList theta center
        (TripleGuideList left middle right) ↔
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right) :=
  vanishesOutsideGuide_tripleGuideList_iff theta center
    left middle right

theorem vanishesOutsideGuide_additiveTripleGuideList_iff_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) :
    VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta) ↔
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta) :=
  vanishesOutsideGuide_additiveTripleGuideList_iff theta center
    rho delta

theorem mem_tripleGuideSet_middle_closed {Center : Type*}
    (left middle right : Center) :
    middle ∈ TripleGuideSet left middle right :=
  mem_tripleGuideSet_middle left middle right

theorem mem_tripleGuideSet_left_closed {Center : Type*}
    (left middle right : Center) :
    left ∈ TripleGuideSet left middle right :=
  mem_tripleGuideSet_left left middle right

theorem mem_tripleGuideSet_right_closed {Center : Type*}
    (left middle right : Center) :
    right ∈ TripleGuideSet left middle right :=
  mem_tripleGuideSet_right left middle right

theorem mem_additiveTripleGuideSet_middle_closed
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) :
    rho ∈ AdditiveTripleGuideSet rho delta :=
  mem_additiveTripleGuideSet_middle rho delta

theorem mem_additiveTripleGuideSet_left_closed
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) :
    rho - delta ∈ AdditiveTripleGuideSet rho delta :=
  mem_additiveTripleGuideSet_left rho delta

theorem mem_additiveTripleGuideSet_right_closed
    {Center : Type*} [Sub Center] [Add Center]
    (rho delta : Center) :
    rho + delta ∈ AdditiveTripleGuideSet rho delta :=
  mem_additiveTripleGuideSet_right rho delta

theorem theta_eq_zero_of_center_not_mem_tripleGuideList_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (TripleGuideList left middle right))
    {row : Row}
    (hcenter : center row ∉ TripleGuideList left middle right) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideList theta center
    left middle right hzero hcenter

theorem theta_eq_zero_of_center_not_mem_additiveTripleGuideList_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row}
    (hcenter : center row ∉ AdditiveTripleGuideList rho delta) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveTripleGuideList theta center
    rho delta hzero hcenter

theorem theta_eq_zero_of_center_not_mem_tripleGuideSet_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right))
    {row : Row}
    (hcenter : center row ∉ TripleGuideSet left middle right) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet theta center
    left middle right hzero hcenter

theorem theta_eq_zero_of_center_ne_tripleGuideSet_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right))
    {row : Row}
    (hleft : center row ≠ left)
    (hmiddle : center row ≠ middle)
    (hright : center row ≠ right) :
    theta row = 0 :=
  theta_eq_zero_of_center_ne_tripleGuideSet theta center
    left middle right hzero hleft hmiddle hright

theorem theta_eq_zero_of_center_not_mem_tripleGuideSet_inter_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row}
    (hcenter :
      center row ∉ (TripleGuideSet left middle right ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet_inter theta center
    left middle right allowedCenters hzero hcenter

theorem theta_eq_zero_of_center_ne_tripleGuideSet_inter_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row}
    (hleft : center row ≠ left)
    (hmiddle : center row ≠ middle)
    (hright : center row ≠ right) :
    theta row = 0 :=
  theta_eq_zero_of_center_ne_tripleGuideSet_inter theta center
    left middle right allowedCenters hzero hleft hmiddle hright

theorem theta_eq_zero_of_center_not_mem_allowed_tripleGuideSet_inter_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row}
    (hallowed : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_allowed_tripleGuideSet_inter theta center
    left middle right allowedCenters hzero hallowed

theorem theta_eq_zero_of_center_not_mem_additiveTripleGuideSet_inter_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveTripleGuideSet_inter theta center
    rho delta allowedCenters hzero hcenter

theorem theta_eq_zero_of_center_ne_additiveTripleGuideSet_inter_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row}
    (hleft : center row ≠ rho - delta)
    (hmiddle : center row ≠ rho)
    (hright : center row ≠ rho + delta) :
    theta row = 0 :=
  theta_eq_zero_of_center_ne_additiveTripleGuideSet_inter theta center
    rho delta allowedCenters hzero hleft hmiddle hright

theorem theta_eq_zero_of_center_not_mem_allowed_additiveTripleGuideSet_inter_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row}
    (hallowed : center row ∉ allowedCenters) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_allowed_additiveTripleGuideSet_inter
    theta center rho delta allowedCenters hzero hallowed

theorem guideLocalityOfNonzero_triple_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right))
    {row : Row} (hne : theta row ≠ 0) :
    center row = left ∨ center row = middle ∨ center row = right :=
  guideLocalityOfNonzero_triple theta center left middle right hzero hne

theorem guideLocalityOfNonzero_tripleGuideList_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (TripleGuideList left middle right))
    {row : Row} (hne : theta row ≠ 0) :
    center row = left ∨ center row = middle ∨ center row = right :=
  guideLocalityOfNonzero_tripleGuideList theta center
    left middle right hzero hne

theorem guideLocalityOfNonzero_additiveTripleGuideList_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row} (hne : theta row ≠ 0) :
    center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta :=
  guideLocalityOfNonzero_additiveTripleGuideList theta center
    rho delta hzero hne

theorem guideLocalityOfNonzero_triple_inter_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    (left middle right : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (TripleGuideSet left middle right ∩ allowedCenters))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = left ∨ center row = middle ∨ center row = right) ∧
    center row ∈ allowedCenters :=
  guideLocalityOfNonzero_triple_inter theta center
    left middle right allowedCenters hzero hne

theorem theta_eq_zero_of_center_not_mem_tripleGuideSet_inter_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (left middle right : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ TripleGuideSet left middle right ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter :
      center row ∉ (TripleGuideSet left middle right ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_tripleGuideSet_inter_subset theta center
    left middle right allowedCenters hsubset hzero hcenter

theorem guideLocalityOfNonzero_triple_inter_subset_closed
    {Row Center Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (left middle right : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ TripleGuideSet left middle right ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = left ∨ center row = middle ∨ center row = right) ∧
    center row ∈ allowedCenters :=
  guideLocalityOfNonzero_triple_inter_subset theta center
    left middle right allowedCenters hsubset hzero hne

theorem guideLocalityOfNonzero_additiveTriple_inter_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hzero :
      VanishesOutsideGuide theta center
        (AdditiveTripleGuideSet rho delta ∩ allowedCenters))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_additiveTriple_inter theta center
    rho delta allowedCenters hzero hne

theorem theta_eq_zero_of_center_not_mem_additiveGuide_inter_subset_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveGuide_inter_subset theta center
    rho delta allowedCenters hsubset hzero hcenter

theorem guideLocalityOfNonzero_additiveGuide_inter_subset_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {actualCenters : Set Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      actualCenters ⊆ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_additiveGuide_inter_subset theta center
    rho delta allowedCenters hsubset hzero hne

theorem theta_eq_zero_of_center_not_mem_additiveGuide_inter_list_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      ∀ c : Center, c ∈ centers →
        c ∈ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveGuide_inter_list theta center
    rho delta allowedCenters hsubset hzero hcenter

theorem guideLocalityOfNonzero_additiveGuide_inter_list_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    {centers : List Center}
    (rho delta : Center) (allowedCenters : Set Center)
    (hsubset :
      ∀ c : Center, c ∈ centers →
        c ∈ AdditiveTripleGuideSet rho delta ∩ allowedCenters)
    (hzero : VanishesOutsideGuideList theta center centers)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_additiveGuide_inter_list theta center
    rho delta allowedCenters hsubset hzero hne

theorem theta_eq_zero_of_center_not_mem_additiveTripleGuideList_inter_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hallowed :
      ∀ c : Center, c ∈ AdditiveTripleGuideList rho delta →
        c ∈ allowedCenters)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row}
    (hcenter :
      center row ∉ (AdditiveTripleGuideSet rho delta ∩ allowedCenters)) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_additiveTripleGuideList_inter
    theta center rho delta allowedCenters hallowed hzero hcenter

theorem guideLocalityOfNonzero_additiveTripleGuideList_inter_closed
    {Row Center Value : Type*} [Zero Value] [Sub Center] [Add Center]
    (theta : Row → Value) (center : Row → Center)
    (rho delta : Center) (allowedCenters : Set Center)
    (hallowed :
      ∀ c : Center, c ∈ AdditiveTripleGuideList rho delta →
        c ∈ allowedCenters)
    (hzero :
      VanishesOutsideGuideList theta center
        (AdditiveTripleGuideList rho delta))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - delta ∨ center row = rho ∨
      center row = rho + delta) ∧
      center row ∈ allowedCenters :=
  guideLocalityOfNonzero_additiveTripleGuideList_inter theta center
    rho delta allowedCenters hallowed hzero hne

theorem ordinaryHighEvenRowGuideCenters_eq_closed {D : Nat}
    (rho : ZMod D) (row : OrdinaryHighEvenRow) :
    ordinaryHighEvenRowGuideCenters rho row =
      AdditiveTripleGuideList rho (ordinaryHighEvenRowDelta row) :=
  ordinaryHighEvenRowGuideCenters_eq rho row

theorem mem_ordinaryHighEvenRowGuideCenters_iff_closed {D : Nat}
    (rho c : ZMod D) (row : OrdinaryHighEvenRow) :
    c ∈ ordinaryHighEvenRowGuideCenters rho row ↔
      c = rho - ordinaryHighEvenRowDelta row ∨ c = rho ∨
        c = rho + ordinaryHighEvenRowDelta row :=
  mem_ordinaryHighEvenRowGuideCenters_iff rho c row

theorem ordinaryHighEvenRowBoundary_subset_support_closed {D : Nat}
    (row : OrdinaryHighEvenRow) :
    ∀ c : ZMod D, c ∈ ordinaryHighEvenRowBoundary row →
      c ∈ ordinaryHighEvenRowSupport row :=
  ordinaryHighEvenRowBoundary_subset_support row

theorem ordinaryHighEvenRowBoundary_length_le_three_closed {D : Nat}
    (row : OrdinaryHighEvenRow) :
    (ordinaryHighEvenRowBoundary (D := D) row).length ≤ 3 :=
  ordinaryHighEvenRowBoundary_length_le_three row

theorem ordinaryHighEvenRowCutVisible_mem_boundary_closed {D : Nat}
    (row : OrdinaryHighEvenRow) :
    @ordinaryHighEvenRowCutVisible D row ∈
      @ordinaryHighEvenRowBoundary D row :=
  ordinaryHighEvenRowCutVisible_mem_boundary row

theorem ordinaryHighEvenRowCutZeroSide_subset_boundary_closed {D : Nat}
    (row : OrdinaryHighEvenRow) :
    ∀ z : ZMod D, z ∈ ordinaryHighEvenRowCutZeroSide row →
      z ∈ ordinaryHighEvenRowBoundary row :=
  ordinaryHighEvenRowCutZeroSide_subset_boundary row

theorem ordinaryHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible_closed
    {D : Nat} (row : OrdinaryHighEvenRow) {z : ZMod D}
    (hz : z ∈ ordinaryHighEvenRowBoundary row)
    (hne : z ≠ ordinaryHighEvenRowCutVisible row) :
    z ∈ ordinaryHighEvenRowCutZeroSide row :=
  ordinaryHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible row hz hne

theorem ordinaryHighEvenRowNonzeroPairs_endpoints_mem_boundary_closed
    {D : Nat} (row : OrdinaryHighEvenRow) {p : ZMod D × ZMod D}
    (hp : p ∈ ordinaryHighEvenRowNonzeroPairs row) :
    p.1 ∈ ordinaryHighEvenRowBoundary row ∧
      p.2 ∈ ordinaryHighEvenRowBoundary row :=
  ordinaryHighEvenRowNonzeroPairs_endpoints_mem_boundary row hp

theorem ordinaryHighEvenRowNonzeroPairs_of_boundary_visible_endpoint_closed
    {D : Nat} (row : OrdinaryHighEvenRow) {p : ZMod D × ZMod D}
    (hboundary :
      p.1 ∈ ordinaryHighEvenRowBoundary row ∧
        p.2 ∈ ordinaryHighEvenRowBoundary row)
    (hvisible :
      p.1 = ordinaryHighEvenRowCutVisible row ∨
        p.2 = ordinaryHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2) :
    p ∈ ordinaryHighEvenRowNonzeroPairs row :=
  ordinaryHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
    row hboundary hvisible hne

theorem ordinaryHighEvenBoundaryAvoidingPhaseChoice_spec_closed
    {D : Nat} (hD : 11 ≤ D) (row : OrdinaryHighEvenRow) :
    OrdinaryHighEvenBoundaryAvoidingPhase
      (ordinaryHighEvenBoundaryAvoidingPhaseChoice (D := D) row) row :=
  ordinaryHighEvenBoundaryAvoidingPhaseChoice_spec hD row

theorem mem_ordinaryHighEvenBoundaryGuideSet_iff_closed {D : Nat}
    (rho c : ZMod D) (row : OrdinaryHighEvenRow) :
    c ∈ ordinaryHighEvenBoundaryGuideSet rho row ↔
      (c = rho - ordinaryHighEvenRowDelta row ∨ c = rho ∨
        c = rho + ordinaryHighEvenRowDelta row) ∧
        c ∈ ordinaryHighEvenRowBoundary row :=
  mem_ordinaryHighEvenBoundaryGuideSet_iff rho c row

theorem not_mem_ordinaryHighEvenBoundaryGuideSet_of_avoiding_closed
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho row)
    (c : ZMod D) :
    c ∉ ordinaryHighEvenBoundaryGuideSet rho row :=
  not_mem_ordinaryHighEvenBoundaryGuideSet_of_avoiding
    rho row havoid c

theorem ordinaryHighEvenBoundaryGuideSet_eq_empty_of_avoiding_closed
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho row) :
    ordinaryHighEvenBoundaryGuideSet rho row = ∅ :=
  ordinaryHighEvenBoundaryGuideSet_eq_empty_of_avoiding
    rho row havoid

theorem ordinaryHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint_closed
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    {p : ZMod D × ZMod D} {c : ZMod D}
    (hp : p ∈ ordinaryHighEvenRowNonzeroPairs row)
    (hcGuide : c ∈ ordinaryHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ ordinaryHighEvenBoundaryGuideSet rho row :=
  ordinaryHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
    rho row hp hcGuide hcEndpoint

theorem ordinaryHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint_closed
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    {p : ZMod D × ZMod D} {c : ZMod D}
    (hboundary :
      p.1 ∈ ordinaryHighEvenRowBoundary row ∧
        p.2 ∈ ordinaryHighEvenRowBoundary row)
    (hvisible :
      p.1 = ordinaryHighEvenRowCutVisible row ∨
        p.2 = ordinaryHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2)
    (hcGuide : c ∈ ordinaryHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ ordinaryHighEvenBoundaryGuideSet rho row :=
  ordinaryHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
    rho row hboundary hvisible hne hcGuide hcEndpoint

theorem ordinaryHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint_closed
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    {actualCenters : Set (ZMod D)}
    (hcert :
      ∀ c : ZMod D, c ∈ actualCenters →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary row ∧
            p.2 ∈ ordinaryHighEvenRowBoundary row) ∧
          (p.1 = ordinaryHighEvenRowCutVisible row ∨
            p.2 = ordinaryHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho row :=
  ordinaryHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
    rho row hcert

theorem ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint_closed
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (centers : List (ZMod D))
    (hcert :
      ∀ c : ZMod D, c ∈ centers →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary row ∧
            p.2 ∈ ordinaryHighEvenRowBoundary row) ∧
          (p.1 = ordinaryHighEvenRowCutVisible row ∨
            p.2 = ordinaryHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    ∀ c : ZMod D, c ∈ centers →
      c ∈ ordinaryHighEvenBoundaryGuideSet rho row :=
  ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
    rho row centers hcert

theorem ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate_closed
    {D : Nat} (rho : ZMod D) (row : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate rho row) :
    ∀ c : ZMod D, c ∈ C.centers →
      c ∈ ordinaryHighEvenBoundaryGuideSet rho row :=
  ordinaryHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate
    rho row C

theorem theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (ordinaryHighEvenBoundaryGuideSet rho growthRow))
    {row : Row}
    (hcenter : center row ∉ ordinaryHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide
    theta center rho growthRow hzero hcenter

theorem guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (ordinaryHighEvenBoundaryGuideSet rho growthRow))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - ordinaryHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + ordinaryHighEvenRowDelta growthRow) ∧
      center row ∈ ordinaryHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide
    theta center rho growthRow hzero hne

theorem theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide_subset_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter : center row ∉ ordinaryHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_ordinaryHighEvenBoundaryGuide_subset
    theta center rho growthRow hsubset hzero hcenter

theorem guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide_subset_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - ordinaryHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + ordinaryHighEvenRowDelta growthRow) ∧
      center row ∈ ordinaryHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide_subset
    theta center rho growthRow hsubset hzero hne

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_subset_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho growthRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_subset
    theta center rho growthRow havoid hsubset hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_subset_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet
        (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow) growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_subset
    theta center hD growthRow hsubset hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_list_boundary_visible_endpoint_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (centers : List (ZMod D))
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho growthRow)
    (hcert :
      ∀ c : ZMod D, c ∈ centers →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary growthRow ∧
            p.2 ∈ ordinaryHighEvenRowBoundary growthRow) ∧
          (p.1 = ordinaryHighEvenRowCutVisible growthRow ∨
            p.2 = ordinaryHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters rho growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
    theta center centers rho growthRow havoid hcert hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_list_boundary_visible_endpoint_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (centers : List (ZMod D))
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hcert :
      ∀ c : ZMod D, c ∈ centers →
        ∃ p : ZMod D × ZMod D,
          (p.1 ∈ ordinaryHighEvenRowBoundary growthRow ∧
            p.2 ∈ ordinaryHighEvenRowBoundary growthRow) ∧
          (p.1 = ordinaryHighEvenRowCutVisible growthRow ∨
            p.2 = ordinaryHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ ordinaryHighEvenRowGuideCenters
            (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow)
            growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_list_boundary_visible_endpoint
    theta center centers hD growthRow hcert hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_boundaryVisibleCertificate_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate rho growthRow)
    (havoid : OrdinaryHighEvenBoundaryAvoidingPhase rho growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryAvoiding_boundaryVisibleCertificate
    theta center rho growthRow C havoid hzero row

theorem theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_boundaryVisibleCertificate_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate
      (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow) growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_boundaryVisibleCertificate
    theta center hD growthRow C hzero row

theorem ordinaryHighEvenOldGeneratorCenters_eq_nil_closed {D : Nat}
    (growthRow : OrdinaryHighEvenRow) :
    ordinaryHighEvenOldGeneratorCenters (D := D) growthRow = [] :=
  ordinaryHighEvenOldGeneratorCenters_eq_nil growthRow

theorem theta_eq_zero_of_ordinaryHighEvenOldGenerator_boundaryChoice_closed
    {D : Nat} {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (ordinaryHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_ordinaryHighEvenOldGenerator_boundaryChoice
    theta center hD growthRow hzero row

theorem chainedHighEvenRowGuideCenters_eq_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow) :
    chainedHighEvenRowGuideCenters rho row =
      AdditiveTripleGuideList rho (chainedHighEvenRowDelta row) :=
  chainedHighEvenRowGuideCenters_eq rho row

theorem mem_chainedHighEvenRowGuideCenters_iff_closed
    (rho c : ZMod 9) (row : ChainedHighEvenRow) :
    c ∈ chainedHighEvenRowGuideCenters rho row ↔
      c = rho - chainedHighEvenRowDelta row ∨ c = rho ∨
        c = rho + chainedHighEvenRowDelta row :=
  mem_chainedHighEvenRowGuideCenters_iff rho c row

theorem chainedHighEvenRowBoundary_subset_support_closed
    (row : ChainedHighEvenRow) :
    ∀ c : ZMod 9, c ∈ chainedHighEvenRowBoundary row →
      c ∈ chainedHighEvenRowSupport row :=
  chainedHighEvenRowBoundary_subset_support row

theorem chainedHighEvenRowBoundary_length_le_three_closed
    (row : ChainedHighEvenRow) :
    (chainedHighEvenRowBoundary row).length ≤ 3 :=
  chainedHighEvenRowBoundary_length_le_three row

theorem chainedHighEvenRowCutVisible_mem_boundary_closed
    (row : ChainedHighEvenRow) :
    chainedHighEvenRowCutVisible row ∈
      chainedHighEvenRowBoundary row :=
  chainedHighEvenRowCutVisible_mem_boundary row

theorem chainedHighEvenRowCutZeroSide_subset_boundary_closed
    (row : ChainedHighEvenRow) :
    ∀ z : ZMod 9, z ∈ chainedHighEvenRowCutZeroSide row →
      z ∈ chainedHighEvenRowBoundary row :=
  chainedHighEvenRowCutZeroSide_subset_boundary row

theorem chainedHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible_closed
    (row : ChainedHighEvenRow) {z : ZMod 9}
    (hz : z ∈ chainedHighEvenRowBoundary row)
    (hne : z ≠ chainedHighEvenRowCutVisible row) :
    z ∈ chainedHighEvenRowCutZeroSide row :=
  chainedHighEvenRowBoundary_mem_cutZeroSide_of_ne_visible row hz hne

theorem chainedHighEvenRowNonzeroPairs_endpoints_mem_boundary_closed
    (row : ChainedHighEvenRow) {p : ZMod 9 × ZMod 9}
    (hp : p ∈ chainedHighEvenRowNonzeroPairs row) :
    p.1 ∈ chainedHighEvenRowBoundary row ∧
      p.2 ∈ chainedHighEvenRowBoundary row :=
  chainedHighEvenRowNonzeroPairs_endpoints_mem_boundary row hp

theorem chainedHighEvenRowNonzeroPairs_of_boundary_visible_endpoint_closed
    (row : ChainedHighEvenRow) {p : ZMod 9 × ZMod 9}
    (hboundary :
      p.1 ∈ chainedHighEvenRowBoundary row ∧
        p.2 ∈ chainedHighEvenRowBoundary row)
    (hvisible :
      p.1 = chainedHighEvenRowCutVisible row ∨
        p.2 = chainedHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2) :
    p ∈ chainedHighEvenRowNonzeroPairs row :=
  chainedHighEvenRowNonzeroPairs_of_boundary_visible_endpoint
    row hboundary hvisible hne

theorem chainedHighEvenBoundaryAvoidingPhaseChoice_spec_closed
    (row : ChainedHighEvenRow) :
    ChainedHighEvenBoundaryAvoidingPhase
      (chainedHighEvenBoundaryAvoidingPhaseChoice row) row :=
  chainedHighEvenBoundaryAvoidingPhaseChoice_spec row

theorem mem_chainedHighEvenBoundaryGuideSet_iff_closed
    (rho c : ZMod 9) (row : ChainedHighEvenRow) :
    c ∈ chainedHighEvenBoundaryGuideSet rho row ↔
      (c = rho - chainedHighEvenRowDelta row ∨ c = rho ∨
        c = rho + chainedHighEvenRowDelta row) ∧
        c ∈ chainedHighEvenRowBoundary row :=
  mem_chainedHighEvenBoundaryGuideSet_iff rho c row

theorem not_mem_chainedHighEvenBoundaryGuideSet_of_avoiding_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho row)
    (c : ZMod 9) :
    c ∉ chainedHighEvenBoundaryGuideSet rho row :=
  not_mem_chainedHighEvenBoundaryGuideSet_of_avoiding
    rho row havoid c

theorem chainedHighEvenBoundaryGuideSet_eq_empty_of_avoiding_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho row) :
    chainedHighEvenBoundaryGuideSet rho row = ∅ :=
  chainedHighEvenBoundaryGuideSet_eq_empty_of_avoiding
    rho row havoid

theorem chainedHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    {p : ZMod 9 × ZMod 9} {c : ZMod 9}
    (hp : p ∈ chainedHighEvenRowNonzeroPairs row)
    (hcGuide : c ∈ chainedHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ chainedHighEvenBoundaryGuideSet rho row :=
  chainedHighEvenBoundaryGuideSet_mem_of_nonzeroPair_endpoint
    rho row hp hcGuide hcEndpoint

theorem chainedHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    {p : ZMod 9 × ZMod 9} {c : ZMod 9}
    (hboundary :
      p.1 ∈ chainedHighEvenRowBoundary row ∧
        p.2 ∈ chainedHighEvenRowBoundary row)
    (hvisible :
      p.1 = chainedHighEvenRowCutVisible row ∨
        p.2 = chainedHighEvenRowCutVisible row)
    (hne : p.1 ≠ p.2)
    (hcGuide : c ∈ chainedHighEvenRowGuideCenters rho row)
    (hcEndpoint : c = p.1 ∨ c = p.2) :
    c ∈ chainedHighEvenBoundaryGuideSet rho row :=
  chainedHighEvenBoundaryGuideSet_mem_of_boundary_visible_endpoint
    rho row hboundary hvisible hne hcGuide hcEndpoint

theorem chainedHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    {actualCenters : Set (ZMod 9)}
    (hcert :
      ∀ c : ZMod 9, c ∈ actualCenters →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary row ∧
            p.2 ∈ chainedHighEvenRowBoundary row) ∧
          (p.1 = chainedHighEvenRowCutVisible row ∨
            p.2 = chainedHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho row :=
  chainedHighEvenBoundaryGuideSet_subset_of_boundary_visible_endpoint
    rho row hcert

theorem chainedHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (centers : List (ZMod 9))
    (hcert :
      ∀ c : ZMod 9, c ∈ centers →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary row ∧
            p.2 ∈ chainedHighEvenRowBoundary row) ∧
          (p.1 = chainedHighEvenRowCutVisible row ∨
            p.2 = chainedHighEvenRowCutVisible row) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters rho row ∧
          (c = p.1 ∨ c = p.2)) :
    ∀ c : ZMod 9, c ∈ centers →
      c ∈ chainedHighEvenBoundaryGuideSet rho row :=
  chainedHighEvenBoundaryGuideSet_list_subset_of_boundary_visible_endpoint
    rho row centers hcert

theorem chainedHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate_closed
    (rho : ZMod 9) (row : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate rho row) :
    ∀ c : ZMod 9, c ∈ C.centers →
      c ∈ chainedHighEvenBoundaryGuideSet rho row :=
  chainedHighEvenBoundaryGuideSet_list_subset_of_boundaryVisibleCertificate
    rho row C

theorem theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (chainedHighEvenBoundaryGuideSet rho growthRow))
    {row : Row}
    (hcenter : center row ∉ chainedHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide
    theta center rho growthRow hzero hcenter

theorem guideLocalityOfNonzero_chainedHighEvenBoundaryGuide_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuide theta center
        (chainedHighEvenBoundaryGuideSet rho growthRow))
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - chainedHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + chainedHighEvenRowDelta growthRow) ∧
      center row ∈ chainedHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_chainedHighEvenBoundaryGuide
    theta center rho growthRow hzero hne

theorem theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide_subset_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row}
    (hcenter : center row ∉ chainedHighEvenBoundaryGuideSet rho growthRow) :
    theta row = 0 :=
  theta_eq_zero_of_center_not_mem_chainedHighEvenBoundaryGuide_subset
    theta center rho growthRow hsubset hzero hcenter

theorem guideLocalityOfNonzero_chainedHighEvenBoundaryGuide_subset_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - chainedHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + chainedHighEvenRowDelta growthRow) ∧
      center row ∈ chainedHighEvenRowBoundary growthRow :=
  guideLocalityOfNonzero_chainedHighEvenBoundaryGuide_subset
    theta center rho growthRow hsubset hzero hne

theorem theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_subset_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho growthRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_subset
    theta center rho growthRow havoid hsubset hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryChoice_subset_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet
        (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow) growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryChoice_subset
    theta center growthRow hsubset hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_list_boundary_visible_endpoint_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (centers : List (ZMod 9))
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho growthRow)
    (hcert :
      ∀ c : ZMod 9, c ∈ centers →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary growthRow ∧
            p.2 ∈ chainedHighEvenRowBoundary growthRow) ∧
          (p.1 = chainedHighEvenRowCutVisible growthRow ∨
            p.2 = chainedHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters rho growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_list_boundary_visible_endpoint
    theta center centers rho growthRow havoid hcert hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryChoice_list_boundary_visible_endpoint_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (centers : List (ZMod 9))
    (growthRow : ChainedHighEvenRow)
    (hcert :
      ∀ c : ZMod 9, c ∈ centers →
        ∃ p : ZMod 9 × ZMod 9,
          (p.1 ∈ chainedHighEvenRowBoundary growthRow ∧
            p.2 ∈ chainedHighEvenRowBoundary growthRow) ∧
          (p.1 = chainedHighEvenRowCutVisible growthRow ∨
            p.2 = chainedHighEvenRowCutVisible growthRow) ∧
          p.1 ≠ p.2 ∧
          c ∈ chainedHighEvenRowGuideCenters
            (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
            growthRow ∧
          (c = p.1 ∨ c = p.2))
    (hzero : VanishesOutsideGuideList theta center centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryChoice_list_boundary_visible_endpoint
    theta center centers growthRow hcert hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_boundaryVisibleCertificate_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate rho growthRow)
    (havoid : ChainedHighEvenBoundaryAvoidingPhase rho growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryAvoiding_boundaryVisibleCertificate
    theta center rho growthRow C havoid hzero row

theorem theta_eq_zero_of_chainedHighEvenBoundaryChoice_boundaryVisibleCertificate_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate
      (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow) growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenBoundaryChoice_boundaryVisibleCertificate
    theta center growthRow C hzero row

theorem chainedHighEvenOldGeneratorCenters_eq_nil_closed
    (growthRow : ChainedHighEvenRow) :
    chainedHighEvenOldGeneratorCenters growthRow = [] :=
  chainedHighEvenOldGeneratorCenters_eq_nil growthRow

theorem theta_eq_zero_of_chainedHighEvenOldGenerator_boundaryChoice_closed
    {Row Value : Type*} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (chainedHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  theta_eq_zero_of_chainedHighEvenOldGenerator_boundaryChoice
    theta center growthRow hzero row

theorem singletonCommon_unique_closed
    {α : Type*} {A B : Set α} {x y : α}
    (hx : IsSingletonCommon A B x)
    (hy : IsSingletonCommon A B y) :
    x = y :=
  singletonCommon_unique hx hy

theorem singletonCommon_iff_inter_eq_singleton_closed
    {α : Type*} {A B : Set α} {x : α} :
    IsSingletonCommon A B x ↔ A ∩ B = ({x} : Set α) :=
  singletonCommon_iff_inter_eq_singleton

theorem singletonSwitchLeft_eq_of_common_image_closed
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c) :
    singletonSwitchLeft G H c = G :=
  singletonSwitchLeft_eq_of_common_image hcommon

theorem singletonSwitchRight_eq_of_common_image_closed
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c) :
    singletonSwitchRight G H c = H :=
  singletonSwitchRight_eq_of_common_image hcommon

theorem singletonCommonEdgeSwitch_identity_closed
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c) :
    singletonSwitchLeft G H c = G ∧ singletonSwitchRight G H c = H :=
  singletonCommonEdgeSwitch_identity hcommon

theorem singletonCommonEdgeSwitch_preserves_singleCycle_closed
    {α : Type*} [DecidableEq α] {G H : α → α} {c : α}
    (hcommon : G c = H c)
    (hG : Shared.IsSingleCycleMap G) (hH : Shared.IsSingleCycleMap H) :
    Shared.IsSingleCycleMap (singletonSwitchLeft G H c) ∧
    Shared.IsSingleCycleMap (singletonSwitchRight G H c) :=
  singletonCommonEdgeSwitch_preserves_singleCycle hcommon hG hH

theorem comparisonMap_apply_closed
    {α : Type*} (T R : α ≃ α) (x : α) :
    comparisonMap T R x = T.symm (R x) :=
  comparisonMap_apply T R x

theorem comparisonMap_symm_closed
    {α : Type*} (T R : α ≃ α) :
    (comparisonMap T R).symm = comparisonMap R T :=
  comparisonMap_symm T R

theorem comparisonSetInvariant_iff_comparisonMap_closed
    {α : Type*} (T R : α ≃ α) (U : Set α) :
    ComparisonSetInvariant T R U ↔
      ∀ x : α, x ∈ U ↔ comparisonMap T R x ∈ U :=
  comparisonSetInvariant_iff_comparisonMap T R U

theorem comparisonMap_fixed_iff_common_image_closed
    {α : Type*} (T R : α ≃ α) (c : α) :
    comparisonMap T R c = c ↔ T c = R c :=
  comparisonMap_fixed_iff_common_image T R c

theorem comparisonMap_fixed_of_common_image_closed
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) :
    comparisonMap T R c = c :=
  comparisonMap_fixed_of_common_image hcommon

theorem common_image_of_comparisonMap_fixed_closed
    {α : Type*} {T R : α ≃ α} {c : α}
    (hfixed : comparisonMap T R c = c) :
    T c = R c :=
  common_image_of_comparisonMap_fixed hfixed

theorem comparisonMap_inverse_fixed_of_common_image_closed
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) :
    comparisonMap R T c = c :=
  comparisonMap_inverse_fixed_of_common_image hcommon

theorem comparisonMap_iterate_fixed_of_common_image_closed
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) (n : Nat) :
    ((comparisonMap T R : α → α)^[n]) c = c :=
  comparisonMap_iterate_fixed_of_common_image hcommon n

theorem comparisonMap_inverse_iterate_fixed_of_common_image_closed
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) (n : Nat) :
    ((comparisonMap R T : α → α)^[n]) c = c :=
  comparisonMap_inverse_iterate_fixed_of_common_image hcommon n

theorem comparisonSetInvariant_singleton_iff_comparisonMap_fixed_closed
    {α : Type*} (T R : α ≃ α) (c : α) :
    ComparisonSetInvariant T R ({c} : Set α) ↔
      comparisonMap T R c = c :=
  comparisonSetInvariant_singleton_iff_comparisonMap_fixed T R c

theorem comparisonSetInvariant_singleton_iff_common_image_closed
    {α : Type*} (T R : α ≃ α) (c : α) :
    ComparisonSetInvariant T R ({c} : Set α) ↔ T c = R c :=
  comparisonSetInvariant_singleton_iff_common_image T R c

theorem comparisonSetInvariant_symm_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) :
    ComparisonSetInvariant R T U :=
  comparisonSetInvariant_symm hU

theorem comparisonSetInvariant_preimage_eq_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) :
    comparisonMap T R ⁻¹' U = U :=
  comparisonSetInvariant_preimage_eq hU

theorem comparisonSetInvariant_iff_preimage_eq_closed
    {α : Type*} (T R : α ≃ α) (U : Set α) :
    ComparisonSetInvariant T R U ↔
      comparisonMap T R ⁻¹' U = U :=
  comparisonSetInvariant_iff_preimage_eq T R U

theorem comparisonSetInvariant_image_eq_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) :
    comparisonMap T R '' U = U :=
  comparisonSetInvariant_image_eq hU

theorem comparisonSetInvariant_iff_image_eq_closed
    {α : Type*} (T R : α ≃ α) (U : Set α) :
    ComparisonSetInvariant T R U ↔
      comparisonMap T R '' U = U :=
  comparisonSetInvariant_iff_image_eq T R U

theorem comparisonSetInvariant_iterate_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : α) :
    x ∈ U ↔ ((comparisonMap T R : α → α)^[n]) x ∈ U :=
  comparisonSetInvariant_iterate hU n x

theorem comparisonSetInvariant_forward_iterate_mem_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : x ∈ U) :
    ((comparisonMap T R : α → α)^[n]) x ∈ U :=
  comparisonSetInvariant_forward_iterate_mem hU hx

theorem comparisonSetInvariant_backward_iterate_mem_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : ((comparisonMap T R : α → α)^[n]) x ∈ U) :
    x ∈ U :=
  comparisonSetInvariant_backward_iterate_mem hU hx

theorem comparisonSetInvariant_iterate_preimage_eq_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) :
    ((comparisonMap T R : α → α)^[n]) ⁻¹' U = U :=
  comparisonSetInvariant_iterate_preimage_eq hU n

theorem comparisonSetInvariant_inverse_iterate_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : α) :
    x ∈ U ↔ ((comparisonMap R T : α → α)^[n]) x ∈ U :=
  comparisonSetInvariant_inverse_iterate hU n x

theorem comparisonSetInvariant_forward_inverse_iterate_mem_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : x ∈ U) :
    ((comparisonMap R T : α → α)^[n]) x ∈ U :=
  comparisonSetInvariant_forward_inverse_iterate_mem hU hx

theorem comparisonSetInvariant_backward_inverse_iterate_mem_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) {n : Nat} {x : α}
    (hx : ((comparisonMap R T : α → α)^[n]) x ∈ U) :
    x ∈ U :=
  comparisonSetInvariant_backward_inverse_iterate_mem hU hx

theorem comparisonSetInvariant_inverse_iterate_preimage_eq_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) (n : Nat) :
    ((comparisonMap R T : α → α)^[n]) ⁻¹' U = U :=
  comparisonSetInvariant_inverse_iterate_preimage_eq hU n

theorem comparisonMapSubtype_apply_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (x : U) :
    comparisonMapSubtype T R U hU x =
      ⟨comparisonMap T R x, (hU x).mp x.property⟩ :=
  comparisonMapSubtype_apply T R U hU x

theorem comparisonMapSubtype_coe_apply_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (x : U) :
    ((comparisonMapSubtype T R U hU x : U) : α) = comparisonMap T R x :=
  comparisonMapSubtype_coe_apply T R U hU x

theorem comparisonMapSubtype_symm_coe_apply_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (x : U) :
    (((comparisonMapSubtype T R U hU).symm x : U) : α) =
      comparisonMap R T x :=
  comparisonMapSubtype_symm_coe_apply T R U hU x

theorem comparisonMapSubtype_iterate_coe_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : U) :
    (((comparisonMapSubtype T R U hU : U → U)^[n]) x : α) =
      ((comparisonMap T R : α → α)^[n]) x :=
  comparisonMapSubtype_iterate_coe T R U hU n x

theorem comparisonMapSubtype_symm_iterate_coe_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    (hU : ComparisonSetInvariant T R U) (n : Nat) (x : U) :
    ((((comparisonMapSubtype T R U hU).symm : U → U)^[n]) x : α) =
      ((comparisonMap R T : α → α)^[n]) x :=
  comparisonMapSubtype_symm_iterate_coe T R U hU n x

theorem comparisonSetInvariant_empty_closed
    {α : Type*} (T R : α ≃ α) :
    ComparisonSetInvariant T R (∅ : Set α) :=
  comparisonSetInvariant_empty T R

theorem comparisonSetInvariant_univ_closed
    {α : Type*} (T R : α ≃ α) :
    ComparisonSetInvariant T R (Set.univ : Set α) :=
  comparisonSetInvariant_univ T R

theorem comparisonSetInvariant_union_closed
    {α : Type*} {T R : α ≃ α} {U V : Set α}
    (hU : ComparisonSetInvariant T R U)
    (hV : ComparisonSetInvariant T R V) :
    ComparisonSetInvariant T R (U ∪ V) :=
  comparisonSetInvariant_union hU hV

theorem comparisonSetInvariant_inter_closed
    {α : Type*} {T R : α ≃ α} {U V : Set α}
    (hU : ComparisonSetInvariant T R U)
    (hV : ComparisonSetInvariant T R V) :
    ComparisonSetInvariant T R (U ∩ V) :=
  comparisonSetInvariant_inter hU hV

theorem comparisonSetInvariant_iUnion_closed
    {ι α : Type*} {T R : α ≃ α} {S : ι → Set α}
    (hS : ∀ i : ι, ComparisonSetInvariant T R (S i)) :
    ComparisonSetInvariant T R (⋃ i : ι, S i) :=
  comparisonSetInvariant_iUnion hS

theorem comparisonSetInvariant_iInter_closed
    {ι α : Type*} {T R : α ≃ α} {S : ι → Set α}
    (hS : ∀ i : ι, ComparisonSetInvariant T R (S i)) :
    ComparisonSetInvariant T R (⋂ i : ι, S i) :=
  comparisonSetInvariant_iInter hS

theorem comparisonSetInvariant_compl_closed
    {α : Type*} {T R : α ≃ α} {U : Set α}
    (hU : ComparisonSetInvariant T R U) :
    ComparisonSetInvariant T R Uᶜ :=
  comparisonSetInvariant_compl hU

theorem comparisonSetInvariant_diff_closed
    {α : Type*} {T R : α ≃ α} {U V : Set α}
    (hU : ComparisonSetInvariant T R U)
    (hV : ComparisonSetInvariant T R V) :
    ComparisonSetInvariant T R (U \ V) :=
  comparisonSetInvariant_diff hU hV

theorem comparisonSetInvariant_singleton_of_common_image_closed
    {α : Type*} {T R : α ≃ α} {c : α}
    (hcommon : T c = R c) :
    ComparisonSetInvariant T R ({c} : Set α) :=
  comparisonSetInvariant_singleton_of_common_image hcommon

theorem partialExchangeLeft_bijective_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) :
    Function.Bijective (partialExchangeLeft T R U) :=
  partialExchangeLeft_bijective T R U hU

theorem partialExchangeRight_bijective_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) :
    Function.Bijective (partialExchangeRight T R U) :=
  partialExchangeRight_bijective T R U hU

theorem partialExchangePair_bijective_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) :
    Function.Bijective (partialExchangeLeft T R U) ∧
      Function.Bijective (partialExchangeRight T R U) :=
  partialExchangePair_bijective T R U hU

theorem partialExchangePair_bijective_singleton_of_common_image_closed
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    Function.Bijective (partialExchangeLeft T R ({c} : Set α)) ∧
      Function.Bijective (partialExchangeRight T R ({c} : Set α)) :=
  partialExchangePair_bijective_singleton_of_common_image T R c hcommon

theorem partialExchangeLeft_singleton_eq_singletonSwitchLeft_closed
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α) :
    partialExchangeLeft T R ({c} : Set α) = singletonSwitchLeft T R c :=
  partialExchangeLeft_singleton_eq_singletonSwitchLeft T R c

theorem partialExchangeRight_singleton_eq_singletonSwitchRight_closed
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α) :
    partialExchangeRight T R ({c} : Set α) = singletonSwitchRight T R c :=
  partialExchangeRight_singleton_eq_singletonSwitchRight T R c

theorem partialExchangePair_identity_singleton_of_common_image_closed
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    partialExchangeLeft T R ({c} : Set α) = T ∧
      partialExchangeRight T R ({c} : Set α) = R :=
  partialExchangePair_identity_singleton_of_common_image T R c hcommon

theorem partialExchangeLeftEquiv_apply_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) (x : α) :
    partialExchangeLeftEquiv T R U hU x = partialExchangeLeft T R U x :=
  partialExchangeLeftEquiv_apply T R U hU x

theorem partialExchangeRightEquiv_apply_closed
    {α : Type*} (T R : α ≃ α) (U : Set α)
    [∀ x, Decidable (x ∈ U)]
    (hU : ComparisonSetInvariant T R U) (x : α) :
    partialExchangeRightEquiv T R U hU x = partialExchangeRight T R U x :=
  partialExchangeRightEquiv_apply T R U hU x

theorem partialExchangeLeftEquiv_singleton_of_common_image_closed
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    partialExchangeLeftEquiv T R ({c} : Set α)
        (comparisonSetInvariant_singleton_of_common_image hcommon) = T :=
  partialExchangeLeftEquiv_singleton_of_common_image T R c hcommon

theorem partialExchangeRightEquiv_singleton_of_common_image_closed
    {α : Type*} [DecidableEq α] (T R : α ≃ α) (c : α)
    (hcommon : T c = R c) :
    partialExchangeRightEquiv T R ({c} : Set α)
        (comparisonSetInvariant_singleton_of_common_image hcommon) = R :=
  partialExchangeRightEquiv_singleton_of_common_image T R c hcommon

theorem supportedOn_fixesOutside_closed
    {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) :
    FixesOutside S f :=
  supportedOn_fixesOutside h

theorem supportedOn_mapsInto_closed
    {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) :
    MapsInto S f :=
  supportedOn_mapsInto h

theorem supportedOn_apply_of_not_mem_closed
    {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) {x : α} (hx : x ∉ S) :
    f x = x :=
  supportedOn_apply_of_not_mem h hx

theorem supportedOn_mem_of_mem_closed
    {α : Type*} {S : Set α} {f : α → α}
    (h : SupportedOn S f) {x : α} (hx : x ∈ S) :
    f x ∈ S :=
  supportedOn_mem_of_mem h hx

theorem fixesOutside_mono_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hST : S ⊆ T) (hf : FixesOutside S f) :
    FixesOutside T f :=
  fixesOutside_mono hST hf

theorem supportedOn_mono_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hST : S ⊆ T) (hf : SupportedOn S f) :
    SupportedOn T f :=
  supportedOn_mono hST hf

theorem fixesOutside_union_left_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : FixesOutside S f) :
    FixesOutside (S ∪ T) f :=
  fixesOutside_union_left hf

theorem fixesOutside_union_right_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : FixesOutside T f) :
    FixesOutside (S ∪ T) f :=
  fixesOutside_union_right hf

theorem supportedOn_union_left_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) :
    SupportedOn (S ∪ T) f :=
  supportedOn_union_left hf

theorem supportedOn_union_right_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn T f) :
    SupportedOn (S ∪ T) f :=
  supportedOn_union_right hf

theorem fixesOutside_comp_closed
    {α : Type*} {S : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside S g) :
    FixesOutside S (fun x => f (g x)) :=
  fixesOutside_comp hf hg

theorem mapsInto_comp_closed
    {α : Type*} {S : Set α} {f g : α → α}
    (hf : MapsInto S f) (hg : MapsInto S g) :
    MapsInto S (fun x => f (g x)) :=
  mapsInto_comp hf hg

theorem supportedOn_comp_closed
    {α : Type*} {S : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn S g) :
    SupportedOn S (fun x => f (g x)) :=
  supportedOn_comp hf hg

theorem fixesOutside_comp_union_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) :
    FixesOutside (S ∪ T) (fun x => f (g x)) :=
  fixesOutside_comp_union hf hg

theorem supportedOn_comp_union_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) :
    SupportedOn (S ∪ T) (fun x => f (g x)) :=
  supportedOn_comp_union hf hg

theorem fixesOutside_comp_union_reverse_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) :
    FixesOutside (S ∪ T) (fun x => g (f x)) :=
  fixesOutside_comp_union_reverse hf hg

theorem supportedOn_comp_union_reverse_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) :
    SupportedOn (S ∪ T) (fun x => g (f x)) :=
  supportedOn_comp_union_reverse hf hg

theorem setsDisjoint_symm_closed
    {α : Type*} {S T : Set α}
    (h : SetsDisjoint S T) :
    SetsDisjoint T S :=
  setsDisjoint_symm h

theorem not_mem_right_of_mem_left_closed
    {α : Type*} {S T : Set α}
    (h : SetsDisjoint S T) {x : α} (hxS : x ∈ S) :
    x ∉ T :=
  not_mem_right_of_mem_left h hxS

theorem not_mem_left_of_mem_right_closed
    {α : Type*} {S T : Set α}
    (h : SetsDisjoint S T) {x : α} (hxT : x ∈ T) :
    x ∉ S :=
  not_mem_left_of_mem_right h hxT

theorem supportedOn_apply_of_mem_disjoint_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T)
    {x : α} (hxT : x ∈ T) :
    f x = x :=
  supportedOn_apply_of_mem_disjoint hf hdisj hxT

theorem mapsInto_of_supportedOn_disjoint_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T) :
    MapsInto T f :=
  mapsInto_of_supportedOn_disjoint hf hdisj

theorem fixesOutside_id_closed
    {α : Type*} (S : Set α) :
    FixesOutside S (fun x : α => x) :=
  fixesOutside_id S

theorem mapsInto_id_closed
    {α : Type*} (S : Set α) :
    MapsInto S (fun x : α => x) :=
  mapsInto_id S

theorem supportedOn_id_closed
    {α : Type*} (S : Set α) :
    SupportedOn S (fun x : α => x) :=
  supportedOn_id S

theorem fixesOutside_iterate_closed
    {α : Type*} {S : Set α} {f : α → α}
    (hf : FixesOutside S f) (n : Nat) :
    FixesOutside S (f^[n]) :=
  fixesOutside_iterate hf n

theorem mapsInto_iterate_closed
    {α : Type*} {S : Set α} {f : α → α}
    (hf : MapsInto S f) (n : Nat) :
    MapsInto S (f^[n]) :=
  mapsInto_iterate hf n

theorem supportedOn_iterate_closed
    {α : Type*} {S : Set α} {f : α → α}
    (hf : SupportedOn S f) (n : Nat) :
    SupportedOn S (f^[n]) :=
  supportedOn_iterate hf n

theorem supportedOn_iterate_apply_of_mem_disjoint_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T)
    (n : Nat) {x : α} (hxT : x ∈ T) :
    (f^[n]) x = x :=
  supportedOn_iterate_apply_of_mem_disjoint hf hdisj n hxT

theorem mapsInto_iterate_of_supportedOn_disjoint_closed
    {α : Type*} {S T : Set α} {f : α → α}
    (hf : SupportedOn S f) (hdisj : SetsDisjoint S T) (n : Nat) :
    MapsInto T (f^[n]) :=
  mapsInto_iterate_of_supportedOn_disjoint hf hdisj n

theorem fixesOutside_iterates_comp_union_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) (n k : Nat) :
    FixesOutside (S ∪ T) (fun x => (f^[n]) ((g^[k]) x)) :=
  fixesOutside_iterates_comp_union hf hg n k

theorem supportedOn_iterates_comp_union_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) (n k : Nat) :
    SupportedOn (S ∪ T) (fun x => (f^[n]) ((g^[k]) x)) :=
  supportedOn_iterates_comp_union hf hg n k

theorem fixesOutside_iterates_comp_union_reverse_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : FixesOutside S f) (hg : FixesOutside T g) (n k : Nat) :
    FixesOutside (S ∪ T) (fun x => (g^[k]) ((f^[n]) x)) :=
  fixesOutside_iterates_comp_union_reverse hf hg n k

theorem supportedOn_iterates_comp_union_reverse_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g) (n k : Nat) :
    SupportedOn (S ∪ T) (fun x => (g^[k]) ((f^[n]) x)) :=
  supportedOn_iterates_comp_union_reverse hf hg n k

theorem commuteOfDisjointSupportedOn_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hdisj : SetsDisjoint S T) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg hdisj

theorem commuteOfDisjointSupportedOn_symmSupports_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hdisj : SetsDisjoint S T) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn_symmSupports hf hg hdisj

theorem commuteOfDisjointSupportedOn_iterates_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hdisj : SetsDisjoint S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg hdisj n k

theorem commuteOfDisjointSupportedOn_iterates_symmSupports_closed
    {α : Type*} {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hdisj : SetsDisjoint S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates_symmSupports hf hg hdisj n k

theorem projectionFiber_mem_closed
    {α β : Type*} (π : α → β) (value : β) (x : α) :
    x ∈ ProjectionFiber π value ↔ π x = value :=
  projectionFiber_mem π value x

theorem productCylinder_mem_closed
    {α β : Type*} (S : Set α) (T : Set β) (x : α × β) :
    x ∈ ProductCylinder S T ↔ x.1 ∈ S ∧ x.2 ∈ T :=
  productCylinder_mem S T x

theorem projectionFiberConstantOn_closed
    {α β : Type*} (π : α → β) (value : β) :
    ProjectionConstantOn π (ProjectionFiber π value) value :=
  projectionFiberConstantOn π value

theorem projectionAvoids_mono_closed
    {α β : Type*} (π : α → β) {S T : Set α} (value : β)
    (hST : S ⊆ T) (hAvoid : ProjectionAvoids π T value) :
    ProjectionAvoids π S value :=
  projectionAvoids_mono π value hST hAvoid

theorem projectionConstantOn_mono_closed
    {α β : Type*} (π : α → β) {S T : Set α} (value : β)
    (hST : S ⊆ T) (hConst : ProjectionConstantOn π T value) :
    ProjectionConstantOn π S value :=
  projectionConstantOn_mono π value hST hConst

theorem projectionImagesDisjoint_mono_closed
    {α β : Type*} (π : α → β) {S S' T T' : Set α}
    (hSS' : S ⊆ S') (hTT' : T ⊆ T')
    (hSep : ProjectionImagesDisjoint π S' T') :
    ProjectionImagesDisjoint π S T :=
  projectionImagesDisjoint_mono π hSS' hTT' hSep

theorem projectionAvoidsOfConstantProjectionNe_closed
    {α β : Type*} (π : α → β) (S : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a) (hne : a ≠ b) :
    ProjectionAvoids π S b :=
  projectionAvoidsOfConstantProjectionNe π S a b hS hne

theorem projectionFiberDisjointOfAvoids_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    (hAvoid : ProjectionAvoids π S value) :
    SetsDisjoint (ProjectionFiber π value) S :=
  projectionFiberDisjointOfAvoids π value S hAvoid

theorem projectionAvoidsOfFiberDisjoint_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    (hDisjoint : SetsDisjoint (ProjectionFiber π value) S) :
    ProjectionAvoids π S value :=
  projectionAvoidsOfFiberDisjoint π value S hDisjoint

theorem projectionAvoids_iff_fiberDisjoint_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α) :
    ProjectionAvoids π S value ↔
      SetsDisjoint (ProjectionFiber π value) S :=
  projectionAvoids_iff_fiberDisjoint π value S

theorem projectionAvoids_iff_disjointFiber_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α) :
    ProjectionAvoids π S value ↔
      SetsDisjoint S (ProjectionFiber π value) :=
  projectionAvoids_iff_disjointFiber π value S

theorem setsDisjointOfProjectionImagesDisjoint_closed
    {α β : Type*} (π : α → β) (S T : Set α)
    (hSep : ProjectionImagesDisjoint π S T) :
    SetsDisjoint S T :=
  setsDisjointOfProjectionImagesDisjoint π S T hSep

theorem projectionImagesDisjoint_symm_closed
    {α β : Type*} (π : α → β) {S T : Set α}
    (hSep : ProjectionImagesDisjoint π S T) :
    ProjectionImagesDisjoint π T S :=
  projectionImagesDisjoint_symm π hSep

theorem projectionImagesDisjointOfConstantProjectionNe_closed
    {α β : Type*} (π : α → β) (S T : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    ProjectionImagesDisjoint π S T :=
  projectionImagesDisjointOfConstantProjectionNe π S T a b hS hT hne

theorem projectionImagesDisjointOfConstantProjectionAvoids_closed
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) :
    ProjectionImagesDisjoint π S T :=
  projectionImagesDisjointOfConstantProjectionAvoids π S T value hS hT

theorem setsDisjointOfConstantProjectionAvoids_closed
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) :
    SetsDisjoint S T :=
  setsDisjointOfConstantProjectionAvoids π S T value hS hT

theorem projectionImagesDisjointOfAvoidsConstantProjection_closed
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) :
    ProjectionImagesDisjoint π S T :=
  projectionImagesDisjointOfAvoidsConstantProjection π S T value hS hT

theorem setsDisjointOfAvoidsConstantProjection_closed
    {α β : Type*} (π : α → β) (S T : Set α) (value : β)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) :
    SetsDisjoint S T :=
  setsDisjointOfAvoidsConstantProjection π S T value hS hT

theorem setsDisjointOfConstantProjectionNe_closed
    {α β : Type*} (π : α → β) (S T : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    SetsDisjoint S T :=
  setsDisjointOfConstantProjectionNe π S T a b hS hT hne

theorem projectionFiberDisjointOfConstantProjectionNe_closed
    {α β : Type*} (π : α → β) (S : Set α) (a b : β)
    (hS : ProjectionConstantOn π S a) (hne : a ≠ b) :
    SetsDisjoint (ProjectionFiber π b) S :=
  projectionFiberDisjointOfConstantProjectionNe π S a b hS hne

theorem productCylinderDisjointOfLeftDisjoint_closed
    {α β : Type*} (S S' : Set α) (T T' : Set β)
    (hS : SetsDisjoint S S') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') :=
  productCylinderDisjointOfLeftDisjoint S S' T T' hS

theorem productCylinderDisjointOfRightDisjoint_closed
    {α β : Type*} (S S' : Set α) (T T' : Set β)
    (hT : SetsDisjoint T T') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') :=
  productCylinderDisjointOfRightDisjoint S S' T T' hT

theorem productCylinderDisjointOfLeftProjectionImagesDisjoint_closed
    {α β γ : Type*} (π : α → γ)
    (S S' : Set α) (T T' : Set β)
    (hSep : ProjectionImagesDisjoint π S S') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') :=
  productCylinderDisjointOfLeftProjectionImagesDisjoint π S S' T T' hSep

theorem productCylinderDisjointOfRightProjectionImagesDisjoint_closed
    {α β γ : Type*} (π : β → γ)
    (S S' : Set α) (T T' : Set β)
    (hSep : ProjectionImagesDisjoint π T T') :
    SetsDisjoint (ProductCylinder S T) (ProductCylinder S' T') :=
  productCylinderDisjointOfRightProjectionImagesDisjoint π S S' T T' hSep

theorem singletonSetsDisjoint_iff_ne_closed
    {α : Type*} {x y : α} :
    SetsDisjoint ({x} : Set α) ({y} : Set α) ↔ x ≠ y :=
  singletonSetsDisjoint_iff_ne

theorem singletonSetsDisjoint_of_ne_closed
    {α : Type*} {x y : α} (hxy : x ≠ y) :
    SetsDisjoint ({x} : Set α) ({y} : Set α) :=
  singletonSetsDisjoint_of_ne hxy

theorem singletonIndexedSetsDisjoint_of_injective_closed
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) :
    SetsDisjoint ({p i} : Set α) ({p j} : Set α) :=
  singletonIndexedSetsDisjoint_of_injective hp hij

theorem productCylinder_singleton_singleton_mem_closed
    {α β : Type*} (a : α) (b : β) (x : α × β) :
    x ∈ ProductCylinder ({a} : Set α) ({b} : Set β) ↔ x = (a, b) :=
  productCylinder_singleton_singleton_mem a b x

theorem productCylinderSingletonSingleton_eq_singleton_closed
    {α β : Type*} (a : α) (b : β) :
    ProductCylinder ({a} : Set α) ({b} : Set β) =
      ({(a, b)} : Set (α × β)) :=
  productCylinderSingletonSingleton_eq_singleton a b

theorem productCylinderSingletonLeftDisjoint_of_ne_closed
    {α β : Type*} {a a' : α} (haa' : a ≠ a')
    (T T' : Set β) :
    SetsDisjoint (ProductCylinder ({a} : Set α) T)
      (ProductCylinder ({a'} : Set α) T') :=
  productCylinderSingletonLeftDisjoint_of_ne haa' T T'

theorem productCylinderSingletonRightDisjoint_of_ne_closed
    {α β : Type*} (S S' : Set α) {b b' : β} (hbb' : b ≠ b') :
    SetsDisjoint (ProductCylinder S ({b} : Set β))
      (ProductCylinder S' ({b'} : Set β)) :=
  productCylinderSingletonRightDisjoint_of_ne S S' hbb'

theorem productCylinderSingletonsDisjoint_of_pair_ne_closed
    {α β : Type*} {a a' : α} {b b' : β}
    (hpair : (a, b) ≠ (a', b')) :
    SetsDisjoint (ProductCylinder ({a} : Set α) ({b} : Set β))
      (ProductCylinder ({a'} : Set α) ({b'} : Set β)) :=
  productCylinderSingletonsDisjoint_of_pair_ne hpair

theorem productCylinderIndexedSingletonsDisjoint_of_injective_pair_closed
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) :
    SetsDisjoint (ProductCylinder ({p i} : Set α) ({q i} : Set β))
      (ProductCylinder ({p j} : Set α) ({q j} : Set β)) :=
  productCylinderIndexedSingletonsDisjoint_of_injective_pair hpq hij

theorem phaseLinePointEquiv_bijective_closed
    {h M : Nat} (k : ZMod h) :
    Function.Bijective (@phaseLinePointEquiv h M k) :=
  phaseLinePointEquiv_bijective k

theorem phaseLinePoint_card_zmod_closed
    {h M : Nat} [NeZero M] (k : ZMod h) :
    @Fintype.card (@PhaseLinePoint h M k)
      (Fintype.ofEquiv (ZMod M) (@phaseLinePointEquiv h M k)) =
        Fintype.card (ZMod M) :=
  phaseLinePoint_card_zmod k

theorem phaseLinePoint_card_closed
    {h M : Nat} [NeZero M] (k : ZMod h) :
    @Fintype.card (@PhaseLinePoint h M k)
      (Fintype.ofEquiv (ZMod M) (@phaseLinePointEquiv h M k)) = M :=
  phaseLinePoint_card k

theorem phaseLineInitialSlot_closed
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) :
    @phaseLineInitialSlot h M n inferInstance k hn =
      fun i => @phaseLinePointEquiv h M k
        ((ZMod.finEquiv M) (Fin.castLE hn i)) :=
  rfl

theorem phaseLineInitialSlot_injective_closed
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) :
    Function.Injective (@phaseLineInitialSlot h M n inferInstance k hn) :=
  phaseLineInitialSlot_injective k hn

theorem phaseLineConstantOn_closed
    {h M : Nat} (k : ZMod h) :
    ProjectionConstantOn (@phaseProjection h M) (@PhaseLine h M k) k :=
  phaseLineConstantOn k

theorem phaseLineDisjointFromLine_closed
    {h M : Nat} {k j : ZMod h} (hkj : k ≠ j) :
    SetsDisjoint (@PhaseLine h M k) (@PhaseLine h M j) :=
  phaseLineDisjointFromLine hkj

theorem phaseTwo_ne_zero_closed
    {h : Nat} [NeZero h] (hh : 2 < h) :
    (2 : ZMod h) ≠ 0 :=
  phaseTwo_ne_zero hh

theorem phaseTwo_ne_one_closed
    {h : Nat} [NeZero h] (hh : 1 < h) :
    (2 : ZMod h) ≠ 1 :=
  phaseTwo_ne_one hh

theorem phaseTwo_ne_negOne_closed
    {h : Nat} [NeZero h] (hh : 3 < h) :
    (2 : ZMod h) ≠ -1 :=
  phaseTwo_ne_negOne hh

theorem phaseReserveLineDisjointFromProtectedStrips_closed
    {h M : Nat} [NeZero h] (hh : 3 < h) :
    SetsDisjoint (@PhaseLine h M (2 : ZMod h))
      (PhaseProtectedStrips h M) :=
  phaseReserveLineDisjointFromProtectedStrips hh

theorem phaseProtectedStripsAvoids_closed
    {h M : Nat} {k : ZMod h}
    (hkNeg : k ≠ -1) (hkZero : k ≠ 0) (hkOne : k ≠ 1) :
    ProjectionAvoids (@phaseProjection h M) (PhaseProtectedStrips h M) k :=
  phaseProtectedStripsAvoids hkNeg hkZero hkOne

theorem phaseProtectedStripsAvoidsReservePhase_closed
    {h M : Nat} [NeZero h] (hh : 3 < h) :
    ProjectionAvoids (@phaseProjection h M)
      (PhaseProtectedStrips h M) (2 : ZMod h) :=
  phaseProtectedStripsAvoidsReservePhase hh

theorem phaseReserveLineProjectionSeparatedFromProtectedStrips_closed
    {h M : Nat} [NeZero h] (hh : 3 < h) :
    ProjectionImagesDisjoint (@phaseProjection h M)
      (@PhaseLine h M (2 : ZMod h)) (PhaseProtectedStrips h M) :=
  phaseReserveLineProjectionSeparatedFromProtectedStrips hh

theorem phaseSetCardCoprimePow_closed
    (m a : Nat) [NeZero m] :
    Nat.Coprime (m - 1) (m ^ a) :=
  phaseSetCardCoprimePow m a

theorem fourPowReserveCapacityShifted_closed
    (n : Nat) :
    2 * (n + 2) + 3 ≤ 4 ^ (n + 2) :=
  fourPowReserveCapacityShifted n

theorem fourPowReserveCapacity_closed
    (a : Nat) (ha : 2 ≤ a) :
    2 * a + 3 ≤ 4 ^ a :=
  fourPowReserveCapacity a ha

theorem phaseReserveCapacity_closed
    (a m : Nat) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    2 * a + 3 ≤ m ^ a :=
  phaseReserveCapacity a m ha hm

theorem phaseReserveLineCapacity_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    2 * a + 3 ≤ @Fintype.card
      (@PhaseLinePoint h (m ^ a) (2 : ZMod h))
      (Fintype.ofEquiv (ZMod (m ^ a))
        (@phaseLinePointEquiv h (m ^ a) (2 : ZMod h))) :=
  phaseReserveLineCapacity h a m ha hm

theorem phaseReserveLineSlot_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseReserveLineSlot h a m inferInstance ha hm =
      @phaseLineInitialSlot h (m ^ a) (2 * a + 3) inferInstance
        (2 : ZMod h) (phaseReserveCapacity a m ha hm) :=
  rfl

theorem phaseReserveLineSlot_injective_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective (@phaseReserveLineSlot h a m inferInstance ha hm) :=
  phaseReserveLineSlot_injective h a m ha hm

theorem phaseReserveLineSlot_phase_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    @phaseProjection h (m ^ a)
      (@phaseReserveLineSlot h a m inferInstance ha hm i).1 =
        (2 : ZMod h) :=
  phaseReserveLineSlot_phase h a m ha hm i

theorem phaseReserveLineSlot_not_mem_protectedStrips_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    (@phaseReserveLineSlot h a m inferInstance ha hm i).1 ∉
      PhaseProtectedStrips h (m ^ a) :=
  phaseReserveLineSlot_not_mem_protectedStrips h a m hh ha hm i

theorem phaseReserveLineSlotList_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseReserveLineSlotList h a m inferInstance ha hm =
      (List.finRange (2 * a + 3)).map
        (@phaseReserveLineSlot h a m inferInstance ha hm) :=
  rfl

theorem phaseReserveLineSlotList_length_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseReserveLineSlotList h a m inferInstance ha hm).length =
      2 * a + 3 :=
  phaseReserveLineSlotList_length h a m ha hm

theorem phaseReserveLineSlotList_nodup_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseReserveLineSlotList h a m inferInstance ha hm).Nodup :=
  phaseReserveLineSlotList_nodup h a m ha hm

theorem phaseReserveLineSlotList_phase_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : @PhaseLinePoint h (m ^ a) (2 : ZMod h)}
    (hx : x ∈ @phaseReserveLineSlotList h a m inferInstance ha hm) :
    @phaseProjection h (m ^ a) x.1 = (2 : ZMod h) :=
  phaseReserveLineSlotList_phase h a m ha hm hx

theorem phaseReserveLineSlotList_not_mem_protectedStrips_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : @PhaseLinePoint h (m ^ a) (2 : ZMod h)}
    (hx : x ∈ @phaseReserveLineSlotList h a m inferInstance ha hm) :
    x.1 ∉ PhaseProtectedStrips h (m ^ a) :=
  phaseReserveLineSlotList_not_mem_protectedStrips h a m hh ha hm hx

theorem phaseReserveLineSlotPointList_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseReserveLineSlotPointList h a m inferInstance ha hm =
      (@phaseReserveLineSlotList h a m inferInstance ha hm).map Subtype.val :=
  rfl

theorem phaseReserveLineSlotPointList_length_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseReserveLineSlotPointList h a m inferInstance ha hm).length =
      2 * a + 3 :=
  phaseReserveLineSlotPointList_length h a m ha hm

theorem phaseReserveLineSlotPointList_nodup_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseReserveLineSlotPointList h a m inferInstance ha hm).Nodup :=
  phaseReserveLineSlotPointList_nodup h a m ha hm

theorem phaseReserveLineSlotPointList_phase_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm) :
    @phaseProjection h (m ^ a) x = (2 : ZMod h) :=
  phaseReserveLineSlotPointList_phase h a m ha hm hx

theorem phaseReserveLineSlotPointList_not_mem_protectedStrips_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm) :
    x ∉ PhaseProtectedStrips h (m ^ a) :=
  phaseReserveLineSlotPointList_not_mem_protectedStrips
    h a m hh ha hm hx

theorem phaseReserveLineSlotPointSet_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseReserveLineSlotPointSet h a m inferInstance ha hm =
      {x | x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm} :=
  rfl

theorem phaseReserveLineSlotPointSet_mem_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : PhaseSection h (m ^ a)) :
    x ∈ @phaseReserveLineSlotPointSet h a m inferInstance ha hm ↔
      x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm :=
  phaseReserveLineSlotPointSet_mem h a m ha hm x

theorem phaseReserveLineSlotPointSet_subsetReserveLine_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseReserveLineSlotPointSet h a m inferInstance ha hm ⊆
      @PhaseLine h (m ^ a) (2 : ZMod h) :=
  phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm

theorem phaseReserveLineSlotPointSet_constantProjection_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn (@phaseProjection h (m ^ a))
      (@phaseReserveLineSlotPointSet h a m inferInstance ha hm)
      (2 : ZMod h) :=
  phaseReserveLineSlotPointSet_constantProjection h a m ha hm

theorem phaseReserveLineSlotPointSet_disjointFromProtectedStrips_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    SetsDisjoint (@phaseReserveLineSlotPointSet h a m inferInstance ha hm)
      (PhaseProtectedStrips h (m ^ a)) :=
  phaseReserveLineSlotPointSet_disjointFromProtectedStrips
    h a m hh ha hm

theorem phaseReserveLineSlotPointSet_mem_iff_exists_slot_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : PhaseSection h (m ^ a)) :
    x ∈ @phaseReserveLineSlotPointSet h a m inferInstance ha hm ↔
      ∃ i : Fin (2 * a + 3),
        (@phaseReserveLineSlot h a m inferInstance ha hm i).1 = x :=
  phaseReserveLineSlotPointSet_mem_iff_exists_slot h a m ha hm x

theorem phaseReserveLineSlotPointSet_slot_unique_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)}
    (hij :
      (@phaseReserveLineSlot h a m inferInstance ha hm i).1 =
        (@phaseReserveLineSlot h a m inferInstance ha hm j).1) :
    i = j :=
  phaseReserveLineSlotPointSet_slot_unique h a m ha hm hij

theorem phaseReserveLineSlotPointSet_exists_unique_slot_closed
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointSet h a m inferInstance ha hm) :
    ∃! i : Fin (2 * a + 3),
      (@phaseReserveLineSlot h a m inferInstance ha hm i).1 = x :=
  phaseReserveLineSlotPointSet_exists_unique_slot h a m ha hm hx

theorem phaseProductLineInitialSlot_closed
    {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) :
    @phaseProductLineInitialSlot Parent parent h M n inferInstance k hn =
      fun i =>
        ⟨(parent, (@phaseLineInitialSlot h M n inferInstance k hn i).1),
          ⟨rfl, (@phaseLineInitialSlot h M n inferInstance k hn i).2⟩⟩ :=
  rfl

theorem phaseProductLineInitialSlot_injective_closed
    {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) :
    Function.Injective
      (@phaseProductLineInitialSlot Parent parent h M n inferInstance k hn) :=
  phaseProductLineInitialSlot_injective parent k hn

theorem phaseProductLineInitialSlot_parent_closed
    {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) (i : Fin n) :
    (@phaseProductLineInitialSlot Parent parent h M n inferInstance k hn i).1.1 =
      parent :=
  phaseProductLineInitialSlot_parent parent k hn i

theorem phaseProductLineInitialSlot_phase_closed
    {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) (i : Fin n) :
    @phaseProjection h M
      (@phaseProductLineInitialSlot Parent parent h M n inferInstance k hn i).1.2 =
        k :=
  phaseProductLineInitialSlot_phase parent k hn i

theorem phaseProductReserveLineSlot_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm =
      @phaseProductLineInitialSlot Parent parent h (m ^ a) (2 * a + 3)
        inferInstance (2 : ZMod h) (phaseReserveCapacity a m ha hm) :=
  rfl

theorem phaseProductReserveLineSlot_injective_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm) :=
  phaseProductReserveLineSlot_injective parent h a m ha hm

theorem phaseProductReserveLineSlot_parent_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1.1 =
      parent :=
  phaseProductReserveLineSlot_parent parent h a m ha hm i

theorem phaseProductReserveLineSlot_phase_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    @phaseProjection h (m ^ a)
      (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1.2 =
        (2 : ZMod h) :=
  phaseProductReserveLineSlot_phase parent h a m ha hm i

theorem phaseProductReserveLineSlot_not_mem_protectedCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) (i : Fin (2 * a + 3)) :
    (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 ∉
      ProductCylinder T (PhaseProtectedStrips h (m ^ a)) :=
  phaseProductReserveLineSlot_not_mem_protectedCylinder parent h a m hh ha hm T i

theorem phaseProductReserveLineSlotList_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm =
      (List.finRange (2 * a + 3)).map
        (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm) :=
  rfl

theorem phaseProductReserveLineSlotList_length_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm).length =
      2 * a + 3 :=
  phaseProductReserveLineSlotList_length parent h a m ha hm

theorem phaseProductReserveLineSlotList_nodup_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm).Nodup :=
  phaseProductReserveLineSlotList_nodup parent h a m ha hm

theorem phaseProductReserveLineSlotList_parent_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm) :
    x.1.1 = parent :=
  phaseProductReserveLineSlotList_parent parent h a m ha hm hx

theorem phaseProductReserveLineSlotList_phase_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm) :
    @phaseProjection h (m ^ a) x.1.2 = (2 : ZMod h) :=
  phaseProductReserveLineSlotList_phase parent h a m ha hm hx

theorem phaseProductReserveLineSlotList_not_mem_protectedCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm) :
    x.1 ∉ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) :=
  phaseProductReserveLineSlotList_not_mem_protectedCylinder
    parent h a m hh ha hm T hx

theorem phaseProductReserveLineSlotPointList_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseProductReserveLineSlotPointList
        Parent parent h a m inferInstance ha hm =
      (@phaseProductReserveLineSlotList
        Parent parent h a m inferInstance ha hm).map Subtype.val :=
  rfl

theorem phaseProductReserveLineSlotPointList_length_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseProductReserveLineSlotPointList
        Parent parent h a m inferInstance ha hm).length =
      2 * a + 3 :=
  phaseProductReserveLineSlotPointList_length parent h a m ha hm

theorem phaseProductReserveLineSlotPointList_nodup_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (@phaseProductReserveLineSlotPointList
        Parent parent h a m inferInstance ha hm).Nodup :=
  phaseProductReserveLineSlotPointList_nodup parent h a m ha hm

theorem phaseProductReserveLineSlotPointList_parent_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointList
      Parent parent h a m inferInstance ha hm) :
    x.1 = parent :=
  phaseProductReserveLineSlotPointList_parent parent h a m ha hm hx

theorem phaseProductReserveLineSlotPointList_phase_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointList
      Parent parent h a m inferInstance ha hm) :
    @phaseProjection h (m ^ a) x.2 = (2 : ZMod h) :=
  phaseProductReserveLineSlotPointList_phase parent h a m ha hm hx

theorem phaseProductReserveLineSlotPointList_not_mem_protectedCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointList
      Parent parent h a m inferInstance ha hm) :
    x ∉ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) :=
  phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
    parent h a m hh ha hm T hx

theorem phaseProductReserveLineSlotPointSet_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm =
      {x | x ∈ @phaseProductReserveLineSlotPointList
        Parent parent h a m inferInstance ha hm} :=
  rfl

theorem phaseProductReserveLineSlotPointSet_mem_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ @phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm ↔
      x ∈ @phaseProductReserveLineSlotPointList
        Parent parent h a m inferInstance ha hm :=
  phaseProductReserveLineSlotPointSet_mem parent h a m ha hm x

theorem phaseProductReserveLineSlotPointSet_subsetReserveCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    @phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm ⊆
      ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h)) :=
  phaseProductReserveLineSlotPointSet_subsetReserveCylinder
    parent h a m ha hm

theorem phaseProductReserveLineSlotPointSet_constantParentProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) parent :=
  phaseProductReserveLineSlotPointSet_constantParentProjection
    parent h a m ha hm

theorem phaseProductReserveLineSlotPointSet_constantPhaseProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) =>
        @phaseProjection h (m ^ a) x.2)
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) (2 : ZMod h) :=
  phaseProductReserveLineSlotPointSet_constantPhaseProjection
    parent h a m ha hm

theorem phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm)
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
    parent h a m hh ha hm T

theorem phaseProductReserveLineSlotPointSet_mem_iff_exists_slot_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ @phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm ↔
      ∃ i : Fin (2 * a + 3),
        (@phaseProductReserveLineSlot
          Parent parent h a m inferInstance ha hm i).1 = x :=
  phaseProductReserveLineSlotPointSet_mem_iff_exists_slot
    parent h a m ha hm x

theorem phaseProductReserveLineSlotPointSet_slot_unique_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)}
    (hij :
      (@phaseProductReserveLineSlot
        Parent parent h a m inferInstance ha hm i).1 =
        (@phaseProductReserveLineSlot
          Parent parent h a m inferInstance ha hm j).1) :
    i = j :=
  phaseProductReserveLineSlotPointSet_slot_unique
    parent h a m ha hm hij

theorem phaseProductReserveLineSlotPointSet_exists_unique_slot_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointSet
      Parent parent h a m inferInstance ha hm) :
    ∃! i : Fin (2 * a + 3),
      (@phaseProductReserveLineSlot
        Parent parent h a m inferInstance ha hm i).1 = x :=
  phaseProductReserveLineSlotPointSet_exists_unique_slot
    parent h a m ha hm hx

theorem phaseProductReserveLineSlotPoint_injective_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) :=
  phaseProductReserveLineSlotPoint_injective parent h a m ha hm

theorem phaseProductReserveLineSlotPair_injective_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) :=
  phaseProductReserveLineSlotPair_injective parent h a m ha hm

theorem phaseProductReserveSupportCertificate_supportSet_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  phaseProductReserveSupportCertificate_supportSet parent h a m hh ha hm

theorem phaseProductReserveSupportCertificate_subsetReserveCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  phaseProductReserveSupportCertificate_subsetReserveCylinder
    parent h a m hh ha hm

theorem phaseProductReserveSupportCertificate_constantParentProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      parent :=
  phaseProductReserveSupportCertificate_constantParentProjection
    parent h a m hh ha hm

theorem phaseProductReserveSupportCertificate_constantPhaseProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      (2 : ZMod h) :=
  phaseProductReserveSupportCertificate_constantPhaseProjection
    parent h a m hh ha hm

theorem phaseProductReserveSupportCertificate_disjointProtected_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  phaseProductReserveSupportCertificate_disjointProtected
    parent h a m hh ha hm T

theorem phaseProductReserveSupportCertificate_existsUniqueSlot_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx :
      x ∈ (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet) :
    ∃! i : Fin (2 * a + 3),
      (phaseProductReserveLineSlot parent h a m ha hm i).1 = x :=
  phaseProductReserveSupportCertificate_existsUniqueSlot
    parent h a m hh ha hm hx

theorem phaseProductReserveSupportCertificate_pointInjective_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) :=
  phaseProductReserveSupportCertificate_pointInjective
    parent h a m hh ha hm

theorem phaseProductReserveSupportCertificate_pairInjective_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) :=
  phaseProductReserveSupportCertificate_pairInjective
    parent h a m hh ha hm

theorem phaseProductReserveSupportCertificate_fixedByProtectedMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    f x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedMap C T hf hx

theorem phaseProductReserveSupportCertificate_fixedByProtectedIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    (f^[n]) x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedIter C T hf n hx

theorem phaseProductReserveSupportCertificate_fixedByProtectedWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    wordEval step word x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedWordEval
    C T step hstep word hx

theorem phaseProductReserveSupportCertificate_fixedByProtectedWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedWordIter
    C T step hstep word n hx

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f) :
    MapsInto C.supportSet f :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedMap C T hf

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) :
    MapsInto C.supportSet (f^[n]) :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedIter C T hf n

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) :
    MapsInto C.supportSet (wordEval step word) :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedWordEval
    C T step hstep word

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) :
    MapsInto C.supportSet ((wordEval step word)^[n]) :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedWordIter
    C T step hstep word n

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    f x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateMap
    C T hf hx

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    (f^[n]) x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateIter
    C T hf n hx

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval step word x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordEval
    C T step hstep word hx

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordIter
    C T step hstep word n hx

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateMap
    C T hf

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (f^[n]) :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateIter
    C T hf n

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval step word) :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordEval
    C T step hstep word

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval step word)^[n]) :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordIter
    C T step hstep word n

theorem phaseProductReserveSupportCertificateProtectedMapsCommute_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g) :
    Function.Commute f g :=
  phaseProductReserveSupportCertificateProtectedMapsCommute C T hf hg

theorem phaseProductReserveSupportCertificateProtectedMapsCommute_symmSupports_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g) :
    Function.Commute f g :=
  phaseProductReserveSupportCertificateProtectedMapsCommute_symmSupports
    C T hf hg

theorem phaseProductReserveSupportCertificateProtectedItersCommute_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseProductReserveSupportCertificateProtectedItersCommute
    C T hf hg n k

theorem phaseProductReserveSupportCertificateProtectedItersCommute_symmSupports_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseProductReserveSupportCertificateProtectedItersCommute_symmSupports
    C T hf hg n k

theorem phaseProductReserveSupportCertificateProtectedWordEvalsCommute_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveSupportCertificateProtectedWordEvalsCommute
    C T leftStep rightStep hleft hright leftWord rightWord

theorem phaseProductReserveSupportCertificateProtectedWordEvalsCommute_symmSupports_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveSupportCertificateProtectedWordEvalsCommute_symmSupports
    C T leftStep rightStep hleft hright leftWord rightWord

theorem phaseProductReserveSupportCertificateProtectedWordItersCommute_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveSupportCertificateProtectedWordItersCommute
    C T leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseProductReserveSupportCertificateProtectedWordItersCommute_symmSupports_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveSupportCertificateProtectedWordItersCommute_symmSupports
    C T leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseDoublingProductSupportInput_holds_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm :=
  phaseDoublingProductSupportInput_holds parent h a m hh ha hm

theorem phaseDoublingProductRealizationInput_holds_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    PhaseDoublingProductRealizationInput parent h a m hh ha hm T
      reserveStep protectedStep reserveWord protectedWord n k :=
  phaseDoublingProductRealizationInput_holds parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord n k

theorem phaseProductReserveLineSlotPointWordEvalsCommute_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveLineSlotPointWordEvalsCommute
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord

theorem phaseProductReserveLineSlotPointWordEvalsCommute_symm_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveLineSlotPointWordEvalsCommute_symm
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord

theorem phaseProductReserveLineSlotPointWordEvalIteratesCommute_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveLineSlotPointWordEvalIteratesCommute
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord n k

theorem phaseProductReserveLineSlotPointWordEvalIteratesCommute_symm_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveLineSlotPointWordEvalIteratesCommute_symm
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord n k

theorem phaseProductReserveLineSlotCylinderWordEvalsCommute_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveLineSlotCylinderWordEvalsCommute
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord

theorem phaseProductReserveLineSlotCylinderWordEvalsCommute_symm_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveLineSlotCylinderWordEvalsCommute_symm
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord

theorem phaseProductReserveLineSlotCylinderWordEvalIteratesCommute_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveLineSlotCylinderWordEvalIteratesCommute
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord n k

theorem phaseProductReserveLineSlotCylinderWordEvalIteratesCommute_symm_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveLineSlotCylinderWordEvalIteratesCommute_symm
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord n k

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedMap_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (i : Fin (2 * a + 3)) :
    f (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 =
      (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 :=
  phaseProductReserveLineSlot_fixedByProtectedSupportedMap
    parent h a m hh ha hm T hf i

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedIterate_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) (i : Fin (2 * a + 3)) :
    (f^[n]) (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 =
      (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 :=
  phaseProductReserveLineSlot_fixedByProtectedSupportedIterate
    parent h a m hh ha hm T hf n i

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedWordEval_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (i : Fin (2 * a + 3)) :
    wordEval step word
        (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 =
      (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 :=
  phaseProductReserveLineSlot_fixedByProtectedSupportedWordEval
    parent h a m hh ha hm T step hstep word i

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedWordEvalIterate_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) (i : Fin (2 * a + 3)) :
    ((wordEval step word)^[n])
        (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 =
      (@phaseProductReserveLineSlot Parent parent h a m inferInstance ha hm i).1 :=
  phaseProductReserveLineSlot_fixedByProtectedSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n i

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedMap_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm) :
    f x.1 = x.1 :=
  phaseProductReserveLineSlotList_fixedByProtectedSupportedMap
    parent h a m hh ha hm T hf hx

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedIterate_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm) :
    (f^[n]) x.1 = x.1 :=
  phaseProductReserveLineSlotList_fixedByProtectedSupportedIterate
    parent h a m hh ha hm T hf n hx

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEval_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm) :
    wordEval step word x.1 = x.1 :=
  phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEval
    parent h a m hh ha hm T step hstep word hx

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ @phaseProductReserveLineSlotList Parent parent h a m inferInstance ha hm) :
    ((wordEval step word)^[n]) x.1 = x.1 :=
  phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n hx

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedMap_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointList
      Parent parent h a m inferInstance ha hm) :
    f x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedMap
    parent h a m hh ha hm T hf hx

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedIterate_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointList
      Parent parent h a m inferInstance ha hm) :
    (f^[n]) x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedIterate
    parent h a m hh ha hm T hf n hx

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEval_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointList
      Parent parent h a m inferInstance ha hm) :
    wordEval step word x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEval
    parent h a m hh ha hm T step hstep word hx

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointList
      Parent parent h a m inferInstance ha hm) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n hx

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedMap_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointSet
      Parent parent h a m inferInstance ha hm) :
    f x = x :=
  phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedMap
    parent h a m hh ha hm T hf hx

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedIterate_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointSet
      Parent parent h a m inferInstance ha hm) :
    (f^[n]) x = x :=
  phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedIterate
    parent h a m hh ha hm T hf n hx

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEval_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointSet
      Parent parent h a m inferInstance ha hm) :
    wordEval step word x = x :=
  phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
    parent h a m hh ha hm T step hstep word hx

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseProductReserveLineSlotPointSet
      Parent parent h a m inferInstance ha hm) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n hx

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedMap_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f) :
    MapsInto
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) f :=
  phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedMap
    parent h a m hh ha hm T hf

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) :
    MapsInto
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) (f^[n]) :=
  phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate
    parent h a m hh ha hm T hf n

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) :
    MapsInto
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) (wordEval step word) :=
  phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval
    parent h a m hh ha hm T step hstep word

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) :
    MapsInto
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) ((wordEval step word)^[n]) :=
  phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n

theorem phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g) :
    Function.Commute f g :=
  phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute
    parent h a m hh ha hm T hf hg

theorem phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) g) :
    Function.Commute f g :=
  phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports
    parent h a m hh ha hm T hf hg

theorem phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute
    parent h a m hh ha hm T hf hg n k

theorem phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports
    parent h a m hh ha hm T hf hg n k

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute
    parent h a m hh ha hm T leftStep rightStep hleft hright
    leftWord rightWord

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute_symmSupports_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute_symmSupports
    parent h a m hh ha hm T leftStep rightStep hleft hright
    leftWord rightWord

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute
    parent h a m hh ha hm T leftStep rightStep hleft hright
    leftWord rightWord n k

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute_symmSupports_closed
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute_symmSupports
    parent h a m hh ha hm T leftStep rightStep hleft hright
    leftWord rightWord n k

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedMap_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    f x = x :=
  phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedMap
    parent h a m hh ha hm T hf hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedMap_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) f) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f :=
  phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedMap
    parent h a m hh ha hm T hf

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedIterate_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    (f^[n]) x = x :=
  phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedIterate
    parent h a m hh ha hm T hf n hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedIterate_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (@phaseProductReserveLineSlotPointSet
        Parent parent h a m inferInstance ha hm) f)
    (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (f^[n]) :=
  phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedIterate
    parent h a m hh ha hm T hf n

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEval_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval step word x = x :=
  phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEval
    parent h a m hh ha hm T step hstep word hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEval_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (step j))
    (word : List ι) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval step word) :=
  phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEval
    parent h a m hh ha hm T step hstep word

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEvalIterate_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate_closed
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseProductReserveLineSlotPointSet
          Parent parent h a m inferInstance ha hm) (step j))
    (word : List ι) (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval step word)^[n]) :=
  phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n

theorem projectionSeparatedSupportedMapsCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hSep : ProjectionImagesDisjoint π S T) :
    Function.Commute f g :=
  projectionSeparatedSupportedMapsCommute π hf hg hSep

theorem projectionSeparatedSupportedMapsCommute_symmSupports_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hSep : ProjectionImagesDisjoint π S T) :
    Function.Commute f g :=
  projectionSeparatedSupportedMapsCommute_symmSupports π hf hg hSep

theorem projectionSeparatedSupportedIteratesCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hSep : ProjectionImagesDisjoint π S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  projectionSeparatedSupportedIteratesCommute π hf hg hSep n k

theorem projectionSeparatedSupportedIteratesCommute_symmSupports_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hSep : ProjectionImagesDisjoint π S T) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  projectionSeparatedSupportedIteratesCommute_symmSupports π hf hg hSep n k

theorem productCylinderLeftDisjointSupportedMapsCommute_closed
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hS : SetsDisjoint S S') :
    Function.Commute f g :=
  productCylinderLeftDisjointSupportedMapsCommute hf hg hS

theorem productCylinderRightDisjointSupportedMapsCommute_closed
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hT : SetsDisjoint T T') :
    Function.Commute f g :=
  productCylinderRightDisjointSupportedMapsCommute hf hg hT

theorem productCylinderLeftProjectionSeparatedSupportedMapsCommute_closed
    {α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π S S') :
    Function.Commute f g :=
  productCylinderLeftProjectionSeparatedSupportedMapsCommute π hf hg hSep

theorem productCylinderRightProjectionSeparatedSupportedMapsCommute_closed
    {α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π T T') :
    Function.Commute f g :=
  productCylinderRightProjectionSeparatedSupportedMapsCommute π hf hg hSep

theorem productCylinderLeftDisjointSupportedIteratesCommute_closed
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hS : SetsDisjoint S S') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderLeftDisjointSupportedIteratesCommute hf hg hS n k

theorem productCylinderRightDisjointSupportedIteratesCommute_closed
    {α β : Type*} {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hT : SetsDisjoint T T') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderRightDisjointSupportedIteratesCommute hf hg hT n k

theorem productCylinderLeftProjectionSeparatedSupportedIteratesCommute_closed
    {α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π S S') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderLeftProjectionSeparatedSupportedIteratesCommute π
    hf hg hSep n k

theorem productCylinderRightProjectionSeparatedSupportedIteratesCommute_closed
    {α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder S T) f)
    (hg : SupportedOn (ProductCylinder S' T') g)
    (hSep : ProjectionImagesDisjoint π T T') (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderRightProjectionSeparatedSupportedIteratesCommute π
    hf hg hSep n k

theorem indexedSingletonSupportedMapsCommute_of_injective_closed
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p i} : Set α) f)
    (hg : SupportedOn ({p j} : Set α) g) :
    Function.Commute f g :=
  indexedSingletonSupportedMapsCommute_of_injective hp hij hf hg

theorem indexedSingletonSupportedMapsCommute_symmSupports_of_injective_closed
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p j} : Set α) f)
    (hg : SupportedOn ({p i} : Set α) g) :
    Function.Commute f g :=
  indexedSingletonSupportedMapsCommute_symmSupports_of_injective
    hp hij hf hg

theorem indexedSingletonSupportedIteratesCommute_of_injective_closed
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p i} : Set α) f)
    (hg : SupportedOn ({p j} : Set α) g) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  indexedSingletonSupportedIteratesCommute_of_injective hp hij hf hg n k

theorem indexedSingletonSupportedIteratesCommute_symmSupports_of_injective_closed
    {ι α : Type*} {p : ι → α} (hp : Function.Injective p)
    {i j : ι} (hij : i ≠ j) {f g : α → α}
    (hf : SupportedOn ({p j} : Set α) f)
    (hg : SupportedOn ({p i} : Set α) g) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  indexedSingletonSupportedIteratesCommute_symmSupports_of_injective
    hp hij hf hg n k

theorem indexedSingletonProductSupportedMapsCommute_of_injective_pair_closed
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) g) :
    Function.Commute f g :=
  indexedSingletonProductSupportedMapsCommute_of_injective_pair
    hpq hij hf hg

theorem indexedSingletonProductSupportedMapsCommute_symmSupports_of_injective_pair_closed
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) g) :
    Function.Commute f g :=
  indexedSingletonProductSupportedMapsCommute_symmSupports_of_injective_pair
    hpq hij hf hg

theorem indexedSingletonProductSupportedIteratesCommute_of_injective_pair_closed
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  indexedSingletonProductSupportedIteratesCommute_of_injective_pair
    hpq hij hf hg n k

theorem indexedSingletonProductSupportedIteratesCommute_symmSupports_of_injective_pair_closed
    {ι α β : Type*} {p : ι → α} {q : ι → β}
    (hpq : Function.Injective (fun i : ι => (p i, q i)))
    {i j : ι} (hij : i ≠ j) {f g : α × β → α × β}
    (hf : SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β)) f)
    (hg : SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  indexedSingletonProductSupportedIteratesCommute_symmSupports_of_injective_pair
    hpq hij hf hg n k

theorem constantProjectionSupportedMapsCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    Function.Commute f g :=
  constantProjectionSupportedMapsCommute π a b hf hg hS hT hne

theorem constantProjectionSupportedMapsCommute_symmSupports_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) :
    Function.Commute f g :=
  constantProjectionSupportedMapsCommute_symmSupports π a b hf hg hS hT hne

theorem constantProjectionSupportedIteratesCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  constantProjectionSupportedIteratesCommute π a b hf hg hS hT hne n k

theorem constantProjectionSupportedIteratesCommute_symmSupports_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (a b : β)
    (hf : SupportedOn T f) (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  constantProjectionSupportedIteratesCommute_symmSupports π a b
    hf hg hS hT hne n k

theorem constantProjectionAvoidsSupportedMapsCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) :
    Function.Commute f g :=
  constantProjectionAvoidsSupportedMapsCommute π value hf hg hS hT

theorem avoidsConstantProjectionSupportedMapsCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) :
    Function.Commute f g :=
  avoidsConstantProjectionSupportedMapsCommute π value hf hg hS hT

theorem constantProjectionAvoidsSupportedIteratesCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  constantProjectionAvoidsSupportedIteratesCommute π value
    hf hg hS hT n k

theorem avoidsConstantProjectionSupportedIteratesCommute_closed
    {α β : Type*} (π : α → β) {S T : Set α} {f g : α → α}
    (value : β)
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  avoidsConstantProjectionSupportedIteratesCommute π value
    hf hg hS hT n k

theorem fiberSeparatedSupportedMapsCommute_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π value) f)
    (hg : SupportedOn S g)
    (hAvoid : ProjectionAvoids π S value) :
    Function.Commute f g :=
  fiberSeparatedSupportedMapsCommute π value S hf hg hAvoid

theorem fiberSeparatedSupportedMapsCommute_symmSupports_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π value) g)
    (hAvoid : ProjectionAvoids π S value) :
    Function.Commute f g :=
  fiberSeparatedSupportedMapsCommute_symmSupports π value S hf hg hAvoid

theorem fiberSeparatedSupportedIteratesCommute_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π value) f)
    (hg : SupportedOn S g)
    (hAvoid : ProjectionAvoids π S value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  fiberSeparatedSupportedIteratesCommute π value S hf hg hAvoid n k

theorem fiberSeparatedSupportedIteratesCommute_symmSupports_closed
    {α β : Type*} (π : α → β) (value : β) (S : Set α)
    {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π value) g)
    (hAvoid : ProjectionAvoids π S value) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  fiberSeparatedSupportedIteratesCommute_symmSupports π value S
    hf hg hAvoid n k

theorem constantAgainstFiberSupportedMapsCommute_closed
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π fiberValue) f)
    (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) :
    Function.Commute f g :=
  constantAgainstFiberSupportedMapsCommute π fiberValue supportValue S
    hf hg hS hne

theorem constantAgainstFiberSupportedMapsCommute_symmSupports_closed
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π fiberValue) g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) :
    Function.Commute f g :=
  constantAgainstFiberSupportedMapsCommute_symmSupports π
    fiberValue supportValue S hf hg hS hne

theorem constantAgainstFiberSupportedIteratesCommute_closed
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn (ProjectionFiber π fiberValue) f)
    (hg : SupportedOn S g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  constantAgainstFiberSupportedIteratesCommute π fiberValue supportValue S
    hf hg hS hne n k

theorem constantAgainstFiberSupportedIteratesCommute_symmSupports_closed
    {α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α) {f g : α → α}
    (hf : SupportedOn S f)
    (hg : SupportedOn (ProjectionFiber π fiberValue) g)
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  constantAgainstFiberSupportedIteratesCommute_symmSupports π
    fiberValue supportValue S hf hg hS hne n k

theorem phaseReserveProtectedSupportedMapsCommute_closed
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (@PhaseLine h M (2 : ZMod h)) f)
    (hg : SupportedOn (PhaseProtectedStrips h M) g) :
    Function.Commute f g :=
  phaseReserveProtectedSupportedMapsCommute hh hf hg

theorem phaseReserveProtectedSupportedMapsCommute_symmSupports_closed
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (PhaseProtectedStrips h M) f)
    (hg : SupportedOn (@PhaseLine h M (2 : ZMod h)) g) :
    Function.Commute f g :=
  phaseReserveProtectedSupportedMapsCommute_symmSupports hh hf hg

theorem phaseReserveProtectedSupportedIteratesCommute_closed
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (@PhaseLine h M (2 : ZMod h)) f)
    (hg : SupportedOn (PhaseProtectedStrips h M) g) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveProtectedSupportedIteratesCommute hh hf hg n k

theorem phaseReserveProtectedSupportedIteratesCommute_symmSupports_closed
    {h M : Nat} [NeZero h] (hh : 3 < h)
    {f g : PhaseSection h M → PhaseSection h M}
    (hf : SupportedOn (PhaseProtectedStrips h M) f)
    (hg : SupportedOn (@PhaseLine h M (2 : ZMod h)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveProtectedSupportedIteratesCommute_symmSupports hh hf hg n k

theorem phaseReserveLineSlot_fixedByProtectedSupportedMap_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (i : Fin (2 * a + 3)) :
    f (@phaseReserveLineSlot h a m inferInstance ha hm i).1 =
      (@phaseReserveLineSlot h a m inferInstance ha hm i).1 :=
  phaseReserveLineSlot_fixedByProtectedSupportedMap h a m hh ha hm hf i

theorem phaseReserveLineSlot_fixedByProtectedSupportedIterate_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat) (i : Fin (2 * a + 3)) :
    (f^[n]) (@phaseReserveLineSlot h a m inferInstance ha hm i).1 =
      (@phaseReserveLineSlot h a m inferInstance ha hm i).1 :=
  phaseReserveLineSlot_fixedByProtectedSupportedIterate
    h a m hh ha hm hf n i

theorem phaseReserveLineSlotList_fixedByProtectedSupportedMap_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    {x : @PhaseLinePoint h (m ^ a) (2 : ZMod h)}
    (hx : x ∈ @phaseReserveLineSlotList h a m inferInstance ha hm) :
    f x.1 = x.1 :=
  phaseReserveLineSlotList_fixedByProtectedSupportedMap
    h a m hh ha hm hf hx

theorem phaseReserveLineSlotList_fixedByProtectedSupportedIterate_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat)
    {x : @PhaseLinePoint h (m ^ a) (2 : ZMod h)}
    (hx : x ∈ @phaseReserveLineSlotList h a m inferInstance ha hm) :
    (f^[n]) x.1 = x.1 :=
  phaseReserveLineSlotList_fixedByProtectedSupportedIterate
    h a m hh ha hm hf n hx

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedMap_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm) :
    f x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedMap
    h a m hh ha hm hf hx

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedIterate_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm) :
    (f^[n]) x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedIterate
    h a m hh ha hm hf n hx

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedMap_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointSet h a m inferInstance ha hm) :
    f x = x :=
  phaseReserveLineSlotPointSet_fixedByProtectedSupportedMap
    h a m hh ha hm hf hx

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedIterate_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointSet h a m inferInstance ha hm) :
    (f^[n]) x = x :=
  phaseReserveLineSlotPointSet_fixedByProtectedSupportedIterate
    h a m hh ha hm hf n hx

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedMap_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f) :
    MapsInto (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) f :=
  phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedMap
    h a m hh ha hm hf

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f) (n : Nat) :
    MapsInto (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (f^[n]) :=
  phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate
    h a m hh ha hm hf n

theorem phaseReserveLineSlotPointSetProtectedSupportedMapsCommute_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) f)
    (hg : SupportedOn (PhaseProtectedStrips h (m ^ a)) g) :
    Function.Commute f g :=
  phaseReserveLineSlotPointSetProtectedSupportedMapsCommute
    h a m hh ha hm hf hg

theorem phaseReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (hg : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) g) :
    Function.Commute f g :=
  phaseReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports
    h a m hh ha hm hf hg

theorem phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) f)
    (hg : SupportedOn (PhaseProtectedStrips h (m ^ a)) g) (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute
    h a m hh ha hm hf hg n k

theorem phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f g : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (PhaseProtectedStrips h (m ^ a)) f)
    (hg : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports
    h a m hh ha hm hf hg n k

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedMap_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) f)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    f x = x :=
  phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedMap
    h a m hh ha hm hf hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedMap_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) f) :
    MapsInto (PhaseProtectedStrips h (m ^ a)) f :=
  phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedMap
    h a m hh ha hm hf

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedIterate_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) f)
    (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    (f^[n]) x = x :=
  phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedIterate
    h a m hh ha hm hf n hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedIterate_closed
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {f : PhaseSection h (m ^ a) → PhaseSection h (m ^ a)}
    (hf : SupportedOn (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) f)
    (n : Nat) :
    MapsInto (PhaseProtectedStrips h (m ^ a)) (f^[n]) :=
  phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedIterate
    h a m hh ha hm hf n

theorem phaseReserveProtectedSupportedWordEvalsCommute_closed
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn (@PhaseLine h M (2 : ZMod h)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn (PhaseProtectedStrips h M) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedSupportedWordEvalsCommute
    hh leftStep rightStep hleft hright leftWord rightWord

theorem phaseReserveProtectedSupportedWordEvalsCommute_symmSupports_closed
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn (PhaseProtectedStrips h M) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn (@PhaseLine h M (2 : ZMod h)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedSupportedWordEvalsCommute_symmSupports
    hh leftStep rightStep hleft hright leftWord rightWord

theorem phaseReserveProtectedSupportedWordEvalIteratesCommute_closed
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn (@PhaseLine h M (2 : ZMod h)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn (PhaseProtectedStrips h M) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedSupportedWordEvalIteratesCommute
    hh leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseReserveProtectedSupportedWordEvalIteratesCommute_symmSupports_closed
    {ι κ : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    (leftStep : ι → PhaseSection h M → PhaseSection h M)
    (rightStep : κ → PhaseSection h M → PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn (PhaseProtectedStrips h M) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn (@PhaseLine h M (2 : ZMod h)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedSupportedWordEvalIteratesCommute_symmSupports
    hh leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute_closed
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute
    h a m hh ha hm leftStep rightStep hleft hright leftWord rightWord

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute_symmSupports_closed
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveLineSlotPointSetProtectedSupportedWordEvalsCommute_symmSupports
    h a m hh ha hm leftStep rightStep hleft hright leftWord rightWord

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute_closed
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute
    h a m hh ha hm leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute_symmSupports_closed
    {ι κ : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (leftStep : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (rightStep : κ → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (PhaseProtectedStrips h (m ^ a)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveLineSlotPointSetProtectedSupportedWordEvalIteratesCommute_symmSupports
    h a m hh ha hm leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEval_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (step j))
    (word : List ι) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    wordEval step word x = x :=
  phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEval
    h a m hh ha hm step hstep word hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEval_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (step j))
    (word : List ι) :
    MapsInto (PhaseProtectedStrips h (m ^ a)) (wordEval step word) :=
  phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEval
    h a m hh ha hm step hstep word

theorem phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEvalIterate_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (step j))
    (word : List ι) (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ PhaseProtectedStrips h (m ^ a)) :
    ((wordEval step word)^[n]) x = x :=
  phaseProtectedStrips_fixedByReserveLineSlotPointSetSupportedWordEvalIterate
    h a m hh ha hm step hstep word n hx

theorem phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (@phaseReserveLineSlotPointSet h a m inferInstance ha hm) (step j))
    (word : List ι) (n : Nat) :
    MapsInto (PhaseProtectedStrips h (m ^ a))
      ((wordEval step word)^[n]) :=
  phaseProtectedStrips_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate
    h a m hh ha hm step hstep word n

theorem phaseReserveLineSlot_fixedByProtectedSupportedWordEval_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (i : Fin (2 * a + 3)) :
    wordEval step word
        (@phaseReserveLineSlot h a m inferInstance ha hm i).1 =
      (@phaseReserveLineSlot h a m inferInstance ha hm i).1 :=
  phaseReserveLineSlot_fixedByProtectedSupportedWordEval
    h a m hh ha hm step hstep word i

theorem phaseReserveLineSlot_fixedByProtectedSupportedWordEvalIterate_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) (i : Fin (2 * a + 3)) :
    ((wordEval step word)^[n])
        (@phaseReserveLineSlot h a m inferInstance ha hm i).1 =
      (@phaseReserveLineSlot h a m inferInstance ha hm i).1 :=
  phaseReserveLineSlot_fixedByProtectedSupportedWordEvalIterate
    h a m hh ha hm step hstep word n i

theorem phaseReserveLineSlotList_fixedByProtectedSupportedWordEval_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι)
    {x : @PhaseLinePoint h (m ^ a) (2 : ZMod h)}
    (hx : x ∈ @phaseReserveLineSlotList h a m inferInstance ha hm) :
    wordEval step word x.1 = x.1 :=
  phaseReserveLineSlotList_fixedByProtectedSupportedWordEval
    h a m hh ha hm step hstep word hx

theorem phaseReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat)
    {x : @PhaseLinePoint h (m ^ a) (2 : ZMod h)}
    (hx : x ∈ @phaseReserveLineSlotList h a m inferInstance ha hm) :
    ((wordEval step word)^[n]) x.1 = x.1 :=
  phaseReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate
    h a m hh ha hm step hstep word n hx

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEval_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm) :
    wordEval step word x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEval
    h a m hh ha hm step hstep word hx

theorem phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointList h a m inferInstance ha hm) :
    ((wordEval step word)^[n]) x = x :=
  phaseReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
    h a m hh ha hm step hstep word n hx

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEval_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointSet h a m inferInstance ha hm) :
    wordEval step word x = x :=
  phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
    h a m hh ha hm step hstep word hx

theorem phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) {x : PhaseSection h (m ^ a)}
    (hx : x ∈ @phaseReserveLineSlotPointSet h a m inferInstance ha hm) :
    ((wordEval step word)^[n]) x = x :=
  phaseReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
    h a m hh ha hm step hstep word n hx

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) :
    MapsInto (@phaseReserveLineSlotPointSet h a m inferInstance ha hm)
      (wordEval step word) :=
  phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval
    h a m hh ha hm step hstep word

theorem phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate_closed
    {ι : Type*} (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step : ι → PhaseSection h (m ^ a) → PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn (PhaseProtectedStrips h (m ^ a)) (step j))
    (word : List ι) (n : Nat) :
    MapsInto (@phaseReserveLineSlotPointSet h a m inferInstance ha hm)
      ((wordEval step word)^[n]) :=
  phaseReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate
    h a m hh ha hm step hstep word n

theorem phaseReserveProtectedProductCylinderSupportedMapsCommute_closed
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn
      (ProductCylinder S (@PhaseLine h M (2 : ZMod h))) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h M)) g) :
    Function.Commute f g :=
  phaseReserveProtectedProductCylinderSupportedMapsCommute hh hf hg

theorem phaseReserveProtectedProductCylinderSupportedMapsCommute_symmSupports_closed
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn (ProductCylinder S (PhaseProtectedStrips h M)) f)
    (hg : SupportedOn
      (ProductCylinder T (@PhaseLine h M (2 : ZMod h))) g) :
    Function.Commute f g :=
  phaseReserveProtectedProductCylinderSupportedMapsCommute_symmSupports hh
    hf hg

theorem phaseReserveProtectedProductCylinderSupportedIteratesCommute_closed
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn
      (ProductCylinder S (@PhaseLine h M (2 : ZMod h))) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h M)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveProtectedProductCylinderSupportedIteratesCommute hh hf hg n k

theorem phaseReserveProtectedProductCylinderSupportedIteratesCommute_symmSupports_closed
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn (ProductCylinder S (PhaseProtectedStrips h M)) f)
    (hg : SupportedOn
      (ProductCylinder T (@PhaseLine h M (2 : ZMod h))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseReserveProtectedProductCylinderSupportedIteratesCommute_symmSupports
    hh hf hg n k

theorem phaseReserveProtectedProductCylinderSupportedWordEvalsCommute_closed
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S (@PhaseLine h M (2 : ZMod h))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h M)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalsCommute
    hh leftStep rightStep hleft hright leftWord rightWord

theorem phaseReserveProtectedProductCylinderSupportedWordEvalsCommute_symmSupports_closed
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S (PhaseProtectedStrips h M)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (@PhaseLine h M (2 : ZMod h))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalsCommute_symmSupports
    hh leftStep rightStep hleft hright leftWord rightWord

theorem phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute_closed
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S (@PhaseLine h M (2 : ZMod h))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h M)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute
    hh leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute_symmSupports_closed
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S (PhaseProtectedStrips h M)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (@PhaseLine h M (2 : ZMod h))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute_symmSupports
    hh leftStep rightStep hleft hright leftWord rightWord n k

theorem wordEval_append_closed
    {ι α : Type*} (step : ι → α → α)
    (left right : List ι) (x : α) :
    wordEval step (left ++ right) x =
      wordEval step right (wordEval step left x) :=
  wordEval_append step left right x

theorem wordEval_bijective_closed
    {ι α : Type*} (step : ι → α → α)
    (hstep : ∀ i : ι, Function.Bijective (step i))
    (word : List ι) :
    Function.Bijective (wordEval step word) :=
  wordEval_bijective step hstep word

theorem fixesOutside_wordEval_closed
    {ι α : Type*} {S : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, FixesOutside S (step i))
    (word : List ι) :
    FixesOutside S (wordEval step word) :=
  fixesOutside_wordEval step hstep word

theorem mapsInto_wordEval_closed
    {ι α : Type*} {S : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, MapsInto S (step i))
    (word : List ι) :
    MapsInto S (wordEval step word) :=
  mapsInto_wordEval step hstep word

theorem supportedOn_wordEval_closed
    {ι α : Type*} {S : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (word : List ι) :
    SupportedOn S (wordEval step word) :=
  supportedOn_wordEval step hstep word

theorem supportedOn_wordEval_apply_of_mem_disjoint_closed
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) {x : α} (hxT : x ∈ T) :
    wordEval step word x = x :=
  supportedOn_wordEval_apply_of_mem_disjoint
    step hstep hdisj word hxT

theorem mapsInto_wordEval_of_supportedOn_disjoint_closed
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) :
    MapsInto T (wordEval step word) :=
  mapsInto_wordEval_of_supportedOn_disjoint step hstep hdisj word

theorem supportedOn_wordEval_iterate_apply_of_mem_disjoint_closed
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) (n : Nat) {x : α} (hxT : x ∈ T) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_wordEval_iterate_apply_of_mem_disjoint
    step hstep hdisj word n hxT

theorem mapsInto_wordEval_iterate_of_supportedOn_disjoint_closed
    {ι α : Type*} {S T : Set α}
    (step : ι → α → α)
    (hstep : ∀ i : ι, SupportedOn S (step i))
    (hdisj : SetsDisjoint S T)
    (word : List ι) (n : Nat) :
    MapsInto T ((wordEval step word)^[n]) :=
  mapsInto_wordEval_iterate_of_supportedOn_disjoint
    step hstep hdisj word n

theorem commuteOfDisjointSupportedWordEvals_closed
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals
    leftStep rightStep hleft hright hdisj leftWord rightWord

theorem commuteOfDisjointSupportedWordEvals_symmSupports_closed
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals_symmSupports
    leftStep rightStep hleft hright hdisj leftWord rightWord

theorem commuteOfDisjointSupportedWordEvalIterates_closed
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright hdisj leftWord rightWord n k

theorem commuteOfDisjointSupportedWordEvalIterates_symmSupports_closed
    {ι κ α : Type*} {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hdisj : SetsDisjoint S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates_symmSupports
    leftStep rightStep hleft hright hdisj leftWord rightWord n k

theorem indexedSingletonSupportedWordEvalsCommute_of_injective_closed
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p i} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p j} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonSupportedWordEvalsCommute_of_injective
    hp hij leftStep rightStep hleft hright leftWord rightWord

theorem indexedSingletonSupportedWordEvalsCommute_symmSupports_of_injective_closed
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p j} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p i} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonSupportedWordEvalsCommute_symmSupports_of_injective
    hp hij leftStep rightStep hleft hright leftWord rightWord

theorem indexedSingletonSupportedWordEvalIteratesCommute_of_injective_closed
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p i} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p j} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonSupportedWordEvalIteratesCommute_of_injective
    hp hij leftStep rightStep hleft hright leftWord rightWord n k

theorem indexedSingletonSupportedWordEvalIteratesCommute_symmSupports_of_injective_closed
    {σ ι κ α : Type*} {p : σ → α} (hp : Function.Injective p)
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ symbol : ι, SupportedOn ({p j} : Set α) (leftStep symbol))
    (hright : ∀ symbol : κ, SupportedOn ({p i} : Set α) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonSupportedWordEvalIteratesCommute_symmSupports_of_injective
    hp hij leftStep rightStep hleft hright leftWord rightWord n k

theorem indexedSingletonProductSupportedWordEvalsCommute_of_injective_pair_closed
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonProductSupportedWordEvalsCommute_of_injective_pair
    hpq hij leftStep rightStep hleft hright leftWord rightWord

theorem indexedSingletonProductSupportedWordEvalsCommute_symmSupports_of_injective_pair_closed
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonProductSupportedWordEvalsCommute_symmSupports_of_injective_pair
    hpq hij leftStep rightStep hleft hright leftWord rightWord

theorem indexedSingletonProductSupportedWordEvalIteratesCommute_of_injective_pair_closed
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonProductSupportedWordEvalIteratesCommute_of_injective_pair
    hpq hij leftStep rightStep hleft hright leftWord rightWord n k

theorem indexedSingletonProductSupportedWordEvalIteratesCommute_symm_of_injective_pair_closed
    {σ ι κ α β : Type*} {p : σ → α} {q : σ → β}
    (hpq : Function.Injective (fun i : σ => (p i, q i)))
    {i j : σ} (hij : i ≠ j)
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ symbol : ι,
      SupportedOn (ProductCylinder ({p j} : Set α) ({q j} : Set β))
        (leftStep symbol))
    (hright : ∀ symbol : κ,
      SupportedOn (ProductCylinder ({p i} : Set α) ({q i} : Set β))
        (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonProductSupportedWordEvalIteratesCommute_symm_of_injective_pair
    hpq hij leftStep rightStep hleft hright leftWord rightWord n k

theorem productCylinderLeftDisjointSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hS : SetsDisjoint S S')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  productCylinderLeftDisjointSupportedWordEvalsCommute
    leftStep rightStep hleft hright hS leftWord rightWord

theorem productCylinderRightDisjointSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hT : SetsDisjoint T T')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  productCylinderRightDisjointSupportedWordEvalsCommute
    leftStep rightStep hleft hright hT leftWord rightWord

theorem productCylinderLeftProjectionSeparatedSupportedWordEvalsCommute_closed
    {ι κ α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π S S')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  productCylinderLeftProjectionSeparatedSupportedWordEvalsCommute
    π leftStep rightStep hleft hright hSep leftWord rightWord

theorem productCylinderRightProjectionSeparatedSupportedWordEvalsCommute_closed
    {ι κ α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π T T')
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  productCylinderRightProjectionSeparatedSupportedWordEvalsCommute
    π leftStep rightStep hleft hright hSep leftWord rightWord

theorem productCylinderLeftDisjointSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hS : SetsDisjoint S S')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  productCylinderLeftDisjointSupportedWordEvalIteratesCommute
    leftStep rightStep hleft hright hS leftWord rightWord n k

theorem productCylinderRightDisjointSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hT : SetsDisjoint T T')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  productCylinderRightDisjointSupportedWordEvalIteratesCommute
    leftStep rightStep hleft hright hT leftWord rightWord n k

theorem productCylinderLeftProjectionSeparatedSupportedWordEvalIteratesCommute_closed
    {ι κ α β γ : Type*} (π : α → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π S S')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  productCylinderLeftProjectionSeparatedSupportedWordEvalIteratesCommute
    π leftStep rightStep hleft hright hSep leftWord rightWord n k

theorem productCylinderRightProjectionSeparatedSupportedWordEvalIteratesCommute_closed
    {ι κ α β γ : Type*} (π : β → γ)
    {S S' : Set α} {T T' : Set β}
    (leftStep : ι → α × β → α × β)
    (rightStep : κ → α × β → α × β)
    (hleft : ∀ i : ι, SupportedOn (ProductCylinder S T) (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProductCylinder S' T') (rightStep j))
    (hSep : ProjectionImagesDisjoint π T T')
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  productCylinderRightProjectionSeparatedSupportedWordEvalIteratesCommute
    π leftStep rightStep hleft hright hSep leftWord rightWord n k

theorem projectionSeparatedSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  projectionSeparatedSupportedWordEvalsCommute π
    leftStep rightStep hleft hright hSep leftWord rightWord

theorem projectionSeparatedSupportedWordEvalsCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  projectionSeparatedSupportedWordEvalsCommute_symmSupports π
    leftStep rightStep hleft hright hSep leftWord rightWord

theorem projectionSeparatedSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  projectionSeparatedSupportedWordEvalIteratesCommute π
    leftStep rightStep hleft hright hSep leftWord rightWord n k

theorem projectionSeparatedSupportedWordEvalIteratesCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hSep : ProjectionImagesDisjoint π S T)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  projectionSeparatedSupportedWordEvalIteratesCommute_symmSupports π
    leftStep rightStep hleft hright hSep leftWord rightWord n k

theorem constantProjectionSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantProjectionSupportedWordEvalsCommute π a b
    leftStep rightStep hleft hright hS hT hne leftWord rightWord

theorem constantProjectionSupportedWordEvalsCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantProjectionSupportedWordEvalsCommute_symmSupports π a b
    leftStep rightStep hleft hright hS hT hne leftWord rightWord

theorem constantProjectionSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantProjectionSupportedWordEvalIteratesCommute π a b
    leftStep rightStep hleft hright hS hT hne leftWord rightWord n k

theorem constantProjectionSupportedWordEvalIteratesCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (a b : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn T (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S a)
    (hT : ProjectionConstantOn π T b)
    (hne : a ≠ b)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantProjectionSupportedWordEvalIteratesCommute_symmSupports π a b
    leftStep rightStep hleft hright hS hT hne leftWord rightWord n k

theorem constantProjectionAvoidsSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantProjectionAvoidsSupportedWordEvalsCommute π value
    leftStep rightStep hleft hright hS hT leftWord rightWord

theorem avoidsConstantProjectionSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  avoidsConstantProjectionSupportedWordEvalsCommute π value
    leftStep rightStep hleft hright hS hT leftWord rightWord

theorem constantProjectionAvoidsSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionConstantOn π S value)
    (hT : ProjectionAvoids π T value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantProjectionAvoidsSupportedWordEvalIteratesCommute π value
    leftStep rightStep hleft hright hS hT leftWord rightWord n k

theorem avoidsConstantProjectionSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} (π : α → β) {S T : Set α}
    (value : β)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn T (rightStep j))
    (hS : ProjectionAvoids π S value)
    (hT : ProjectionConstantOn π T value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  avoidsConstantProjectionSupportedWordEvalIteratesCommute π value
    leftStep rightStep hleft hright hS hT leftWord rightWord n k

theorem fiberSeparatedSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π value) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  fiberSeparatedSupportedWordEvalsCommute π value S
    leftStep rightStep hleft hright hAvoid leftWord rightWord

theorem fiberSeparatedSupportedWordEvalsCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π value) (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  fiberSeparatedSupportedWordEvalsCommute_symmSupports π value S
    leftStep rightStep hleft hright hAvoid leftWord rightWord

theorem fiberSeparatedSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π value) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  fiberSeparatedSupportedWordEvalIteratesCommute π value S
    leftStep rightStep hleft hright hAvoid leftWord rightWord n k

theorem fiberSeparatedSupportedWordEvalIteratesCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) (value : β) (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π value) (rightStep j))
    (hAvoid : ProjectionAvoids π S value)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  fiberSeparatedSupportedWordEvalIteratesCommute_symmSupports π value S
    leftStep rightStep hleft hright hAvoid leftWord rightWord n k

theorem constantAgainstFiberSupportedWordEvalsCommute_closed
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π fiberValue) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantAgainstFiberSupportedWordEvalsCommute π fiberValue supportValue S
    leftStep rightStep hleft hright hS hne leftWord rightWord

theorem constantAgainstFiberSupportedWordEvalsCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π fiberValue) (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  constantAgainstFiberSupportedWordEvalsCommute_symmSupports π fiberValue supportValue S
    leftStep rightStep hleft hright hS hne leftWord rightWord

theorem constantAgainstFiberSupportedWordEvalIteratesCommute_closed
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn (ProjectionFiber π fiberValue) (leftStep i))
    (hright : ∀ j : κ, SupportedOn S (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantAgainstFiberSupportedWordEvalIteratesCommute π fiberValue supportValue S
    leftStep rightStep hleft hright hS hne leftWord rightWord n k

theorem constantAgainstFiberSupportedWordEvalIteratesCommute_symmSupports_closed
    {ι κ α β : Type*} (π : α → β) (fiberValue supportValue : β)
    (S : Set α)
    (leftStep : ι → α → α) (rightStep : κ → α → α)
    (hleft : ∀ i : ι, SupportedOn S (leftStep i))
    (hright : ∀ j : κ, SupportedOn (ProjectionFiber π fiberValue) (rightStep j))
    (hS : ProjectionConstantOn π S supportValue)
    (hne : supportValue ≠ fiberValue)
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  constantAgainstFiberSupportedWordEvalIteratesCommute_symmSupports π fiberValue supportValue S
    leftStep rightStep hleft hright hS hne leftWord rightWord n k

theorem wordEvalSingleCycleOfRank_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (step : ι → α → α) (word : List ι)
    (rank : α ≃ ZMod N)
    (hstep : ∀ x : α, rank (wordEval step word x) = rank x + 1) :
    Shared.IsSingleCycleMap (wordEval step word) :=
  wordEvalSingleCycleOfRank step word rank hstep

theorem wordSkewStep_bijective_closed
    {Symbol Base Fiber : Type*}
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber)
    (hbase : ∀ symbol : Symbol, Function.Bijective (baseStep symbol))
    (hfiber : ∀ symbol : Symbol, ∀ base : Base,
      Function.Bijective (fiberStep symbol base))
    (symbol : Symbol) :
    Function.Bijective (wordSkewStep baseStep fiberStep symbol) :=
  wordSkewStep_bijective baseStep fiberStep hbase hfiber symbol

theorem wordSkewEval_bijective_closed
    {Symbol Base Fiber : Type*}
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber)
    (hbase : ∀ symbol : Symbol, Function.Bijective (baseStep symbol))
    (hfiber : ∀ symbol : Symbol, ∀ base : Base,
      Function.Bijective (fiberStep symbol base))
    (word : List Symbol) :
    Function.Bijective (wordSkewEval baseStep fiberStep word) :=
  wordSkewEval_bijective baseStep fiberStep hbase hfiber word

theorem wordSkewEvalSingleCycleOfRank_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (baseStep : Symbol → Base → Base)
    (fiberStep : Symbol → Base → Fiber → Fiber)
    (word : List Symbol)
    (rank : Base × Fiber ≃ ZMod N)
    (hstep : ∀ x : Base × Fiber,
      rank (wordSkewEval baseStep fiberStep word x) = rank x + 1) :
    Shared.IsSingleCycleMap (wordSkewEval baseStep fiberStep word) :=
  wordSkewEvalSingleCycleOfRank baseStep fiberStep word rank hstep

theorem rowPlacementSupport_mem_closed
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (row : Row)
    (x : Parent × NewCoord) :
    x ∈ rowPlacementSupport placement row ↔ x = placement row :=
  rowPlacementSupport_mem placement row x

theorem rowPlacementSupport_eq_singleton_closed
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (row : Row) :
    rowPlacementSupport placement row =
      ({placement row} : Set (Parent × NewCoord)) :=
  rowPlacementSupport_eq_singleton placement row

theorem rowPlacementSupportSet_closed
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) :
    rowPlacementSupportSet placement =
      ⋃ row, rowPlacementSupport placement row :=
  rfl

theorem rowPlacementSupportSet_eq_iUnion_closed
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) :
    rowPlacementSupportSet placement =
      ⋃ row, rowPlacementSupport placement row :=
  rowPlacementSupportSet_eq_iUnion placement

theorem rowPlacementSupport_subset_supportSet_closed
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (row : Row) :
    rowPlacementSupport placement row ⊆
      rowPlacementSupportSet placement :=
  rowPlacementSupport_subset_supportSet placement row

theorem rowPlacementSupportSet_mem_closed
    {Row Parent NewCoord : Type*}
    (placement : Row → Parent × NewCoord) (x : Parent × NewCoord) :
    x ∈ rowPlacementSupportSet placement ↔
      ∃ row : Row, x = placement row :=
  rowPlacementSupportSet_mem placement x

theorem rowPlacement_ne_of_parent_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1) :
    placement leftRow ≠ placement rightRow :=
  rowPlacement_ne_of_parent_ne hparent

theorem rowPlacement_ne_of_newCoord_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2) :
    placement leftRow ≠ placement rightRow :=
  rowPlacement_ne_of_newCoord_ne hnewCoord

theorem rowPlacementSupports_disjoint_of_injective_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) :=
  rowPlacementSupports_disjoint_of_injective hplacement hrow

theorem rowPlacementSupports_disjoint_of_ne_placement_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) :=
  rowPlacementSupports_disjoint_of_ne_placement hplacement

theorem rowPlacementSupports_disjoint_of_parent_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) :=
  rowPlacementSupports_disjoint_of_parent_ne hparent

theorem rowPlacementSupports_disjoint_of_newCoord_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2) :
    SetsDisjoint (rowPlacementSupport placement leftRow)
      (rowPlacementSupport placement rightRow) :=
  rowPlacementSupports_disjoint_of_newCoord_ne hnewCoord

theorem rowPlacementSupportedMapsCommute_of_injective_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_of_injective
    hplacement hrow hleft hright

theorem rowPlacementSupportedMapsCommute_of_ne_placement_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_of_ne_placement
    hplacement hleft hright

theorem rowPlacementSupportedMapsCommute_of_parent_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_of_parent_ne hparent hleft hright

theorem rowPlacementSupportedMapsCommute_of_newCoord_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_of_newCoord_ne hnewCoord hleft hright

theorem rowPlacementSupportedMapsCommute_symmSupports_of_injective_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_symmSupports_of_injective
    hplacement hrow hleft hright

theorem rowPlacementSupportedMapsCommute_symmSupports_of_ne_placement_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_symmSupports_of_ne_placement
    hplacement hleft hright

theorem rowPlacementSupportedMapsCommute_symmSupports_of_parent_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_symmSupports_of_parent_ne
    hparent hleft hright

theorem rowPlacementSupportedMapsCommute_symmSupports_of_newCoord_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_symmSupports_of_newCoord_ne
    hnewCoord hleft hright

theorem rowPlacementSupportedIteratesCommute_of_injective_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_of_injective
    hplacement hrow hleft hright n k

theorem rowPlacementSupportedIteratesCommute_of_ne_placement_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_of_ne_placement
    hplacement hleft hright n k

theorem rowPlacementSupportedIteratesCommute_of_parent_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_of_parent_ne
    hparent hleft hright n k

theorem rowPlacementSupportedIteratesCommute_of_newCoord_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement leftRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement rightRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_of_newCoord_ne
    hnewCoord hleft hright n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_injective_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_symmSupports_of_injective
    hplacement hrow hleft hright n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_ne_placement_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_symmSupports_of_ne_placement
    hplacement hleft hright n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_parent_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_symmSupports_of_parent_ne
    hparent hleft hright n k

theorem rowPlacementSupportedIteratesCommute_symmSupports_of_newCoord_ne_closed
    {Row Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    {leftMap rightMap : Parent × NewCoord → Parent × NewCoord}
    (hleft : SupportedOn (rowPlacementSupport placement rightRow) leftMap)
    (hright : SupportedOn (rowPlacementSupport placement leftRow) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_symmSupports_of_newCoord_ne
    hnewCoord hleft hright n k

theorem rowPlacementSupportedWordEvalsCommute_of_injective_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_of_injective
    hplacement hrow leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_of_ne_placement_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_of_ne_placement
    hplacement leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_of_parent_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_of_parent_ne
    hparent leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_of_newCoord_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_of_newCoord_ne
    hnewCoord leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_injective_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_symmSupports_of_injective
    hplacement hrow leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_ne_placement_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_symmSupports_of_ne_placement
    hplacement leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_parent_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_symmSupports_of_parent_ne
    hparent leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalsCommute_symmSupports_of_newCoord_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_symmSupports_of_newCoord_ne
    hnewCoord leftStep rightStep hleft hright leftWord rightWord

theorem rowPlacementSupportedWordEvalIteratesCommute_of_injective_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_injective
    hplacement hrow leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_of_ne_placement_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_ne_placement
    hplacement leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_of_parent_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_parent_ne
    hparent leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_of_newCoord_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement leftRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement rightRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_newCoord_ne
    hnewCoord leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_injective_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    (hplacement : Function.Injective placement)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_injective
    hplacement hrow leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_ne_placement_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hplacement : placement leftRow ≠ placement rightRow)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_ne_placement
    hplacement leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_parent_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hparent : (placement leftRow).1 ≠ (placement rightRow).1)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_parent_ne
    hparent leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_newCoord_ne_closed
    {Row SymbolLeft SymbolRight Parent NewCoord : Type*}
    {placement : Row → Parent × NewCoord}
    {leftRow rightRow : Row}
    (hnewCoord : (placement leftRow).2 ≠ (placement rightRow).2)
    (leftStep : SymbolLeft → Parent × NewCoord → Parent × NewCoord)
    (rightStep : SymbolRight → Parent × NewCoord → Parent × NewCoord)
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn (rowPlacementSupport placement rightRow)
          (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn (rowPlacementSupport placement leftRow)
          (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_newCoord_ne
    hnewCoord leftStep rightStep hleft hright
    leftWord rightWord n k

theorem rowWordPlacementCertificate_eval_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) :
    C.eval row = wordEval (C.step row) (C.word row) :=
  rowWordPlacementCertificate_eval C row

theorem rowWordPlacementCertificate_eval_supported_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) :
    SupportedOn (rowPlacementSupport C.placement row)
      (C.eval row) :=
  rowWordPlacementCertificate_eval_supported C row

theorem rowWordPlacementCertificate_step_supportedOn_supportSet_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) (symbol : Symbol) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.step row symbol) :=
  rowWordPlacementCertificate_step_supportedOn_supportSet C row symbol

theorem rowWordPlacementCertificate_eval_supportedOn_supportSet_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (row : Row) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.eval row) :=
  rowWordPlacementCertificate_eval_supportedOn_supportSet C row

theorem rowWordPlacementCertificate_evalWord_supportedOn_supportSet_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (rows : List Row) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (wordEval C.eval rows) :=
  rowWordPlacementCertificate_evalWord_supportedOn_supportSet C rows

theorem rowWordPlacementCertificate_evalWordIter_supportedOn_support_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    (rows : List Row) (n : Nat) :
    SupportedOn (rowPlacementSupportSet C.placement)
      ((wordEval C.eval rows)^[n]) :=
  rowWordPlacementCertificate_evalWordIter_supportedOn_support C rows n

theorem rowWordPlacementCertificate_supports_disjoint_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport C.placement leftRow)
      (rowPlacementSupport C.placement rightRow) :=
  rowWordPlacementCertificate_supports_disjoint C hrow

theorem rowWordPlacementCertificate_evalsCommute_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow) :
    Function.Commute (C.eval leftRow) (C.eval rightRow) :=
  rowWordPlacementCertificate_evalsCommute C hrow

theorem rowWordPlacementCertificate_evalIteratesCommute_closed
    {Row Symbol Parent NewCoord : Type*}
    (C : RowWordPlacementCertificate Row Symbol Parent NewCoord)
    {leftRow rightRow : Row} (hrow : leftRow ≠ rightRow)
    (n k : Nat) :
    Function.Commute ((C.eval leftRow)^[n]) ((C.eval rightRow)^[k]) :=
  rowWordPlacementCertificate_evalIteratesCommute C hrow n k

theorem finRowWordPlacementCertificate_eval_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    C.eval row = wordEval (C.step row) (C.word row) :=
  finRowWordPlacementCertificate_eval C row

theorem finRowWordPlacementCertificate_placement_injective_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord) :
    Function.Injective C.placement :=
  finRowWordPlacementCertificate_placement_injective C

theorem finRowWordPlacementCertificate_eval_supported_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupport C.placement row)
      (C.eval row) :=
  finRowWordPlacementCertificate_eval_supported C row

theorem finRowWordPlacementCertificate_step_supportedOn_supportSet_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) (symbol : Symbol) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.step row symbol) :=
  finRowWordPlacementCertificate_step_supportedOn_supportSet C row symbol

theorem finRowWordPlacementCertificate_eval_supportedOn_supportSet_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.eval row) :=
  finRowWordPlacementCertificate_eval_supportedOn_supportSet C row

theorem finRowWordPlacementCertificate_evalWord_supportedOn_supportSet_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (wordEval C.eval rows) :=
  finRowWordPlacementCertificate_evalWord_supportedOn_supportSet C rows

theorem finRowWordPlacementCertificate_evalWordIter_supportedOn_support_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) (n : Nat) :
    SupportedOn (rowPlacementSupportSet C.placement)
      ((wordEval C.eval rows)^[n]) :=
  finRowWordPlacementCertificate_evalWordIter_supportedOn_support C rows n

theorem finRowWordPlacementCertificate_supports_disjoint_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport C.placement leftRow)
      (rowPlacementSupport C.placement rightRow) :=
  finRowWordPlacementCertificate_supports_disjoint C hrow

theorem finRowWordPlacementCertificate_evalsCommute_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    Function.Commute (C.eval leftRow) (C.eval rightRow) :=
  finRowWordPlacementCertificate_evalsCommute C hrow

theorem finRowWordPlacementCertificate_evalIteratesCommute_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C : FinRowWordPlacementCertificate rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow)
    (n k : Nat) :
    Function.Commute ((C.eval leftRow)^[n]) ((C.eval rightRow)^[k]) :=
  finRowWordPlacementCertificate_evalIteratesCommute C hrow n k

theorem coordinateSeparatedFinRowWordPlacementCertificate_eval_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    C.eval row = wordEval (C.step row) (C.word row) :=
  coordinateSeparatedFinRowWordPlacementCertificate_eval C row

theorem coordinateSeparatedFinRowWordPlacementCertificate_placement_ne_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    C.placement leftRow ≠ C.placement rightRow :=
  coordinateSeparatedFinRowWordPlacementCertificate_placement_ne C hrow

theorem coordinateSeparatedFinRowWordPlacementCertificate_placement_injective_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord) :
    Function.Injective C.placement :=
  coordinateSeparatedFinRowWordPlacementCertificate_placement_injective C

theorem coordinateSeparatedFinRowWordPlacementCertificate_eval_supported_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupport C.placement row)
      (C.eval row) :=
  coordinateSeparatedFinRowWordPlacementCertificate_eval_supported C row

theorem coordinateSeparatedFinRowWordPlacementCertificate_step_supportedOn_supportSet_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) (symbol : Symbol) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.step row symbol) :=
  coordinateSeparatedFinRowWordPlacementCertificate_step_supportedOn_supportSet
    C row symbol

theorem coordinateSeparatedFinRowWordPlacementCertificate_eval_supportedOn_supportSet_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (row : Fin rowCount) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (C.eval row) :=
  coordinateSeparatedFinRowWordPlacementCertificate_eval_supportedOn_supportSet
    C row

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalWord_supportedOn_supportSet_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) :
    SupportedOn (rowPlacementSupportSet C.placement)
      (wordEval C.eval rows) :=
  coordinateSeparatedFinRowWordPlacementCertificate_evalWord_supportedOn_supportSet
    C rows

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalWordIter_supportedOn_support_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    (rows : List (Fin rowCount)) (n : Nat) :
    SupportedOn (rowPlacementSupportSet C.placement)
      ((wordEval C.eval rows)^[n]) :=
  coordinateSeparatedFinRowWordPlacementCertificate_evalWordIter_supportedOn_support
    C rows n

theorem coordinateSeparatedFinRowWordPlacementCertificate_supports_disjoint_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    SetsDisjoint (rowPlacementSupport C.placement leftRow)
      (rowPlacementSupport C.placement rightRow) :=
  coordinateSeparatedFinRowWordPlacementCertificate_supports_disjoint
    C hrow

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalsCommute_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow) :
    Function.Commute (C.eval leftRow) (C.eval rightRow) :=
  coordinateSeparatedFinRowWordPlacementCertificate_evalsCommute C hrow

theorem coordinateSeparatedFinRowWordPlacementCertificate_evalIteratesCommute_closed
    {rowCount : Nat} {Symbol Parent NewCoord : Type*}
    (C :
      CoordinateSeparatedFinRowWordPlacementCertificate
        rowCount Symbol Parent NewCoord)
    {leftRow rightRow : Fin rowCount} (hrow : leftRow ≠ rightRow)
    (n k : Nat) :
    Function.Commute ((C.eval leftRow)^[n]) ((C.eval rightRow)^[k]) :=
  coordinateSeparatedFinRowWordPlacementCertificate_evalIteratesCommute
    C hrow n k

theorem endpointReservePlacement_parent_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    (endpointReservePlacement parent h a m ha hm i).1 = parent :=
  endpointReservePlacement_parent parent h a m ha hm i

theorem endpointReservePlacement_phase_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    phaseProjection (endpointReservePlacement parent h a m ha hm i).2 =
      (2 : ZMod h) :=
  endpointReservePlacement_phase parent h a m ha hm i

theorem endpointReservePlacement_injective_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective (endpointReservePlacement parent h a m ha hm) :=
  endpointReservePlacement_injective parent h a m ha hm

theorem endpointReservePlacement_newCoord_ne_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j) :
    (endpointReservePlacement parent h a m ha hm i).2 ≠
      (endpointReservePlacement parent h a m ha hm j).2 :=
  endpointReservePlacement_newCoord_ne parent h a m ha hm hij

theorem endpointReservePlacement_coordinateSeparated_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j) :
    (endpointReservePlacement parent h a m ha hm i).1 ≠
        (endpointReservePlacement parent h a m ha hm j).1 ∨
      (endpointReservePlacement parent h a m ha hm i).2 ≠
        (endpointReservePlacement parent h a m ha hm j).2 :=
  endpointReservePlacement_coordinateSeparated parent h a m ha hm hij

theorem endpointReservePlacementList_length_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (endpointReservePlacementList parent h a m ha hm).length =
      2 * a + 3 :=
  endpointReservePlacementList_length parent h a m ha hm

theorem endpointReservePlacementList_nodup_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (endpointReservePlacementList parent h a m ha hm).Nodup :=
  endpointReservePlacementList_nodup parent h a m ha hm

theorem endpointReservePlacementList_parent_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    x.1 = parent :=
  endpointReservePlacementList_parent parent h a m ha hm hx

theorem endpointReservePlacementList_phase_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    phaseProjection x.2 = (2 : ZMod h) :=
  endpointReservePlacementList_phase parent h a m ha hm hx

theorem endpointReservePlacementList_not_mem_protectedCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    x ∉ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) :=
  endpointReservePlacementList_not_mem_protectedCylinder
    parent h a m hh ha hm T hx

theorem endpointReservePlacementList_mem_iff_exists_slot_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointReservePlacementList parent h a m ha hm ↔
      ∃ i : Fin (2 * a + 3),
        endpointReservePlacement parent h a m ha hm i = x :=
  endpointReservePlacementList_mem_iff_exists_slot parent h a m ha hm x

theorem endpointReservePlacementList_exists_unique_slot_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    ∃! i : Fin (2 * a + 3),
      endpointReservePlacement parent h a m ha hm i = x :=
  endpointReservePlacementList_exists_unique_slot parent h a m ha hm hx

theorem endpointReservePlacementSupportSet_eq_phaseProduct_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    endpointReservePlacementSupportSet parent h a m ha hm =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  endpointReservePlacementSupportSet_eq_phaseProduct parent h a m ha hm

theorem endpointReservePlacementSupportSet_mem_iff_exists_row_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointReservePlacementSupportSet parent h a m ha hm ↔
      ∃ i : Fin (2 * a + 3),
        endpointReservePlacement parent h a m ha hm i = x :=
  endpointReservePlacementSupportSet_mem_iff_exists_row
    parent h a m ha hm x

theorem endpointReservePlacementSupportSet_exists_unique_row_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementSupportSet parent h a m ha hm) :
    ∃! i : Fin (2 * a + 3),
      endpointReservePlacement parent h a m ha hm i = x :=
  endpointReservePlacementSupportSet_exists_unique_row
    parent h a m ha hm hx

theorem endpointReservePlacementSupportSet_eq_iUnion_rowPlacementSupport_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    endpointReservePlacementSupportSet parent h a m ha hm =
      ⋃ i : Fin (2 * a + 3),
        rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i :=
  endpointReservePlacementSupportSet_eq_iUnion_rowPlacementSupport
    parent h a m ha hm

theorem endpointReservePlacementSupportSet_subsetReserveCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    endpointReservePlacementSupportSet parent h a m ha hm ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  endpointReservePlacementSupportSet_subsetReserveCylinder
    parent h a m ha hm

theorem endpointReservePlacementSupportSet_constantParentProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (endpointReservePlacementSupportSet parent h a m ha hm)
      parent :=
  endpointReservePlacementSupportSet_constantParentProjection
    parent h a m ha hm

theorem endpointReservePlacementSupportSet_constantPhaseProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (2 : ZMod h) :=
  endpointReservePlacementSupportSet_constantPhaseProjection
    parent h a m ha hm

theorem endpointReservePlacementSupportSet_disjointProtected_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  endpointReservePlacementSupportSet_disjointProtected
    parent h a m hh ha hm T

theorem endpointReservePlacementSupportCertificate_supportSet_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm :=
  endpointReservePlacementSupportCertificate_supportSet
    parent h a m hh ha hm

theorem endpointReservePlacementSupportCertificate_supportSet_phaseProduct_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  endpointReservePlacementSupportCertificate_supportSet_phaseProduct
    parent h a m hh ha hm

theorem endpointReservePlacementSupportCertificate_supportSet_iUnionRows_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet =
      ⋃ i : Fin (2 * a + 3),
        rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i :=
  endpointReservePlacementSupportCertificate_supportSet_iUnionRows
    parent h a m hh ha hm

theorem endpointReservePlacementSupportCertificate_subsetReserveCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  endpointReservePlacementSupportCertificate_subsetReserveCylinder
    parent h a m hh ha hm

theorem endpointReservePlacementSupportCertificate_constantParentProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet
      parent :=
  endpointReservePlacementSupportCertificate_constantParentProjection
    parent h a m hh ha hm

theorem endpointReservePlacementSupportCertificate_constantPhaseProjection_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet
      (2 : ZMod h) :=
  endpointReservePlacementSupportCertificate_constantPhaseProjection
    parent h a m hh ha hm

theorem endpointReservePlacementSupportCertificate_disjointProtected_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint
      (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  endpointReservePlacementSupportCertificate_disjointProtected
    parent h a m hh ha hm T

theorem endpointReservePlacementSupportCertificate_existsUniqueRow_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx :
      x ∈ (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet) :
    ∃! i : Fin (2 * a + 3),
      endpointReservePlacement parent h a m ha hm i = x :=
  endpointReservePlacementSupportCertificate_existsUniqueRow
    parent h a m hh ha hm hx

theorem endpointReservePlacementSupportCertificate_placementInjective_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective (endpointReservePlacement parent h a m ha hm) :=
  endpointReservePlacementSupportCertificate_placementInjective
    parent h a m hh ha hm

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_supportSet_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    C.toPhaseProductCert.supportSet = C.supportSet :=
  endpointReservePlacementSupportCertificate_toPhaseProductCert_supportSet C

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_phaseProduct_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    C.toPhaseProductCert.supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  endpointReservePlacementSupportCertificate_toPhaseProductCert_phaseProduct C

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_disjointProtected_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent) :
    SetsDisjoint C.toPhaseProductCert.supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  endpointReservePlacementSupportCertificate_toPhaseProductCert_disjointProtected
    C T

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_existsUniqueSlot_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toPhaseProductCert.supportSet) :
    ∃! i : Fin (2 * a + 3),
      (phaseProductReserveLineSlot parent h a m ha hm i).1 = x :=
  endpointReservePlacementSupportCertificate_toPhaseProductCert_existsUniqueSlot
    C hx

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_pointInjective_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) :=
  endpointReservePlacementSupportCertificate_toPhaseProductCert_pointInjective C

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_pairInjective_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) :=
  endpointReservePlacementSupportCertificate_toPhaseProductCert_pairInjective C

theorem endpointReservePlacementSupportCertificate_fixedByProtectedMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    f x = x :=
  endpointReservePlacementSupportCertificate_fixedByProtectedMap C T hf hx

theorem endpointReservePlacementSupportCertificate_fixedByProtectedIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    (f^[n]) x = x :=
  endpointReservePlacementSupportCertificate_fixedByProtectedIter
    C T hf n hx

theorem endpointReservePlacementSupportCertificate_fixedByProtectedWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    wordEval step word x = x :=
  endpointReservePlacementSupportCertificate_fixedByProtectedWordEval
    C T step hstep word hx

theorem endpointReservePlacementSupportCertificate_fixedByProtectedWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    ((wordEval step word)^[n]) x = x :=
  endpointReservePlacementSupportCertificate_fixedByProtectedWordIter
    C T step hstep word n hx

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f) :
    MapsInto C.supportSet f :=
  endpointReservePlacementSupportCertificate_mapsIntoProtectedMap C T hf

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) :
    MapsInto C.supportSet (f^[n]) :=
  endpointReservePlacementSupportCertificate_mapsIntoProtectedIter C T hf n

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) :
    MapsInto C.supportSet (wordEval step word) :=
  endpointReservePlacementSupportCertificate_mapsIntoProtectedWordEval
    C T step hstep word

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) :
    MapsInto C.supportSet ((wordEval step word)^[n]) :=
  endpointReservePlacementSupportCertificate_mapsIntoProtectedWordIter
    C T step hstep word n

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    f x = x :=
  endpointProtectedCylinder_fixedByReservePlacementSupportCertificateMap
    C T hf hx

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    (f^[n]) x = x :=
  endpointProtectedCylinder_fixedByReservePlacementSupportCertificateIter
    C T hf n hx

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval step word x = x :=
  endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordEval
    C T step hstep word hx

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval step word)^[n]) x = x :=
  endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordIter
    C T step hstep word n hx

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateMap_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f :=
  endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateMap
    C T hf

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateIter_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (f^[n]) :=
  endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateIter
    C T hf n

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordEval_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval step word) :=
  endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordEval
    C T step hstep word

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordIter_closed
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval step word)^[n]) :=
  endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordIter
    C T step hstep word n

theorem endpointReservePlacementSupportCertificateProtectedMapsCommute_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g) :
    Function.Commute f g :=
  endpointReservePlacementSupportCertificateProtectedMapsCommute C T hf hg

theorem endpointReservePlacementSupportCertificateProtectedMapsCommute_symmSupports_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g) :
    Function.Commute f g :=
  endpointReservePlacementSupportCertificateProtectedMapsCommute_symmSupports
    C T hf hg

theorem endpointReservePlacementSupportCertificateProtectedItersCommute_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReservePlacementSupportCertificateProtectedItersCommute
    C T hf hg n k

theorem endpointReservePlacementSupportCertificateProtectedItersCommute_symmSupports_closed
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReservePlacementSupportCertificateProtectedItersCommute_symmSupports
    C T hf hg n k

theorem endpointReservePlacementSupportCertificateProtectedWordEvalsCommute_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReservePlacementSupportCertificateProtectedWordEvalsCommute
    C T leftStep rightStep hleft hright leftWord rightWord

theorem endpointReservePlacementSupportCertificateProtectedWordEvalsCommute_symmSupports_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReservePlacementSupportCertificateProtectedWordEvalsCommute_symmSupports
    C T leftStep rightStep hleft hright leftWord rightWord

theorem endpointReservePlacementSupportCertificateProtectedWordItersCommute_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReservePlacementSupportCertificateProtectedWordItersCommute
    C T leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReservePlacementSupportCertificateProtectedWordItersCommute_symmSupports_closed
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReservePlacementSupportCertificateProtectedWordItersCommute_symmSupports
    C T leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedPlacement_inl_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (row : Fin (2 * a + 3)) :
    endpointReserveAugmentedPlacement
      parent h a m ha hm extraPlacement (Sum.inl row) =
      endpointReservePlacement parent h a m ha hm row :=
  endpointReserveAugmentedPlacement_inl
    parent h a m ha hm extraPlacement row

theorem endpointReserveAugmentedPlacement_inr_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (row : ExtraRow) :
    endpointReserveAugmentedPlacement
      parent h a m ha hm extraPlacement (Sum.inr row) =
      extraPlacement row :=
  endpointReserveAugmentedPlacement_inr
    parent h a m ha hm extraPlacement row

theorem endpointReserveAugmentedPlacement_injective_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (extraInjective : Function.Injective extraPlacement)
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a))) :
    Function.Injective
      (endpointReserveAugmentedPlacement
        parent h a m ha hm extraPlacement) :=
  endpointReserveAugmentedPlacement_injective
    parent h a m hh ha hm extraPlacement extraInjective extraProtected

theorem endpointExtraPlacementSupportSet_mem_iff_exists_row_closed
    {ExtraRow Parent : Type*} {h a m : Nat}
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointExtraPlacementSupportSet extraPlacement ↔
      ∃ row : ExtraRow, extraPlacement row = x :=
  endpointExtraPlacementSupportSet_mem_iff_exists_row
    extraPlacement x

theorem endpointExtraPlacementSupportSet_subsetProtected_closed
    {ExtraRow Parent : Type*} {h a m : Nat}
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a))) :
    endpointExtraPlacementSupportSet extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointExtraPlacementSupportSet_subsetProtected
    extraPlacement extraProtected

theorem endpointReserveAugmentedSupportSet_eq_iUnionRows_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a)) :
    endpointReserveAugmentedSupportSet
      parent h a m ha hm extraPlacement =
      ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm extraPlacement) row :=
  endpointReserveAugmentedSupportSet_eq_iUnionRows
    parent h a m ha hm extraPlacement

theorem endpointReserveAugmentedSupportSet_mem_iff_exists_row_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointReserveAugmentedSupportSet
      parent h a m ha hm extraPlacement ↔
      ∃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement row = x :=
  endpointReserveAugmentedSupportSet_mem_iff_exists_row
    parent h a m ha hm extraPlacement x

theorem endpointReserveAugmentedSupportSet_eq_union_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a)) :
    endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet extraPlacement :=
  endpointReserveAugmentedSupportSet_eq_union
    parent h a m ha hm extraPlacement

theorem endpointReserveAugmentedSupportSet_reserveSubset_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a)) :
    endpointReservePlacementSupportSet parent h a m ha hm ⊆
      endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement :=
  endpointReserveAugmentedSupportSet_reserveSubset
    parent h a m ha hm extraPlacement

theorem endpointReserveAugmentedSupportSet_extraSubset_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a)) :
    endpointExtraPlacementSupportSet extraPlacement ⊆
      endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement :=
  endpointReserveAugmentedSupportSet_extraSubset
    parent h a m ha hm extraPlacement

theorem endpointReserveAugmentedSupportSet_extraSubsetProtected_closed
    {ExtraRow Parent : Type*} (h a m : Nat) [NeZero m]
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a))) :
    endpointExtraPlacementSupportSet extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedSupportSet_extraSubsetProtected
    h a m extraPlacement extraProtected

theorem endpointReserveAugmentedSupportSet_exists_unique_row_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (placementInjective :
      Function.Injective
        (endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement))
    {x : Parent × PhaseSection h (m ^ a)}
    (hx :
      x ∈ endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement) :
    ∃! row : Sum (Fin (2 * a + 3)) ExtraRow,
      endpointReserveAugmentedPlacement
        parent h a m ha hm extraPlacement row = x :=
  endpointReserveAugmentedSupportSet_exists_unique_row
    parent h a m ha hm extraPlacement placementInjective hx

theorem endpointReserveAugmentedSupportSet_supports_disjoint_closed
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (extraPlacement : ExtraRow → Parent × PhaseSection h (m ^ a))
    (extraInjective : Function.Injective extraPlacement)
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a)))
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement) rightRow) :=
  endpointReserveAugmentedSupportSet_supports_disjoint
    parent h a m hh ha hm extraPlacement
    extraInjective extraProtected hrow

theorem endpointReserveAugmentedSupportCertificate_supportSet_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    C.supportSet =
      endpointReserveAugmentedSupportSet
        parent h a m ha hm C.extraPlacement :=
  endpointReserveAugmentedSupportCertificate_supportSet C

theorem endpointReserveAugmentedSupportCertificate_supportSet_union_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    C.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedSupportCertificate_supportSet_union C

theorem endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    C.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows C

theorem endpointReserveAugmentedSupportCertificate_placement_injective_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    Function.Injective
      (endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement) :=
  endpointReserveAugmentedSupportCertificate_placement_injective C

theorem endpointReserveAugmentedSupportCertificate_reserveSubset_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    endpointReservePlacementSupportSet parent h a m ha hm ⊆
      C.supportSet :=
  endpointReserveAugmentedSupportCertificate_reserveSubset C

theorem endpointReserveAugmentedSupportCertificate_extraSubset_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆ C.supportSet :=
  endpointReserveAugmentedSupportCertificate_extraSubset C

theorem endpointReserveAugmentedSupportCertificate_extraSubsetProtected_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedSupportCertificate_extraSubsetProtected C

theorem endpointReserveAugmentedSupportCertificate_existsUniqueRow_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) ExtraRow,
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedSupportCertificate_existsUniqueRow C hx

theorem endpointReserveAugmentedSupportCertificate_supports_disjoint_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  endpointReserveAugmentedSupportCertificate_supports_disjoint C hrow

theorem endpointReserveAugmentedSupportCertificate_rowSupportSubset_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row ⊆
      C.supportSet :=
  endpointReserveAugmentedSupportCertificate_rowSupportSubset C row

theorem endpointReserveAugmentedSupportCertificate_reserveRowSupportSubset_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow) ⊆
      endpointReservePlacementSupportSet parent h a m ha hm :=
  endpointReserveAugmentedSupportCertificate_reserveRowSupportSubset
    C reserveRow

theorem endpointReserveAugmentedSupportCertificate_extraRowSupportSubset_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) :
    rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow) ⊆
      endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedSupportCertificate_extraRowSupportSubset
    C extraRow

theorem endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C

theorem endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint_symm_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint_symm C

theorem endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute C hf hg

theorem endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute_symmSupports_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute_symmSupports
    C hf hg

theorem endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute
    C hf hg n k

theorem endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute_symmSupports_closed
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute_symmSupports
    C hf hg n k

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute_closed
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute_symmSupports_closed
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute_symmSupports
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute_closed
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute_symmSupports_closed
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute_symmSupports
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedRowWordCertificate_supportSet_union_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedRowWordCertificate_supportSet_union C

theorem endpointReserveAugmentedRowWordCertificate_supportSet_iUnionRows_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  endpointReserveAugmentedRowWordCertificate_supportSet_iUnionRows C

theorem endpointReserveAugmentedRowWordCertificate_supportExtraProtected_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedRowWordCertificate_supportExtraProtected C

theorem endpointReserveAugmentedRowWordCertificate_supportExistsUniqueRow_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toSupportCertificate.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) ExtraRow,
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedRowWordCertificate_supportExistsUniqueRow C hx

theorem endpointReserveAugmentedRowWordCertificate_placement_injective_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    Function.Injective
      (endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement) :=
  endpointReserveAugmentedRowWordCertificate_placement_injective C

theorem endpointReserveAugmentedRowWordCertificate_eval_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    C.toRowWordPlacementCertificate.eval row =
      wordEval (C.step row) (C.word row) :=
  endpointReserveAugmentedRowWordCertificate_eval C row

theorem endpointReserveAugmentedRowWordCertificate_eval_supported_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    SupportedOn
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row)
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedRowWordCertificate_eval_supported C row

theorem endpointReserveAugmentedRowWordCertificate_step_supportedOn_supportSet_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) (symbol : Symbol) :
    SupportedOn C.toSupportCertificate.supportSet (C.step row symbol) :=
  endpointReserveAugmentedRowWordCertificate_step_supportedOn_supportSet
    C row symbol

theorem endpointReserveAugmentedRowWordCertificate_eval_supportedOn_supportSet_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    SupportedOn C.toSupportCertificate.supportSet
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedRowWordCertificate_eval_supportedOn_supportSet
    C row

theorem endpointReserveAugmentedRowWordCertificate_evalWord_supportedOn_supportSet_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) ExtraRow)) :
    SupportedOn C.toSupportCertificate.supportSet
      (wordEval (fun row => C.toRowWordPlacementCertificate.eval row) rows) :=
  endpointReserveAugmentedRowWordCertificate_evalWord_supportedOn_supportSet
    C rows

theorem endpointReserveAugmentedRowWordCertificate_evalWord_iterate_supportedOn_supportSet_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) ExtraRow)) (n : Nat) :
    SupportedOn C.toSupportCertificate.supportSet
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval row) rows)^[n]) :=
  endpointReserveAugmentedRowWordCertificate_evalWord_iterate_supportedOn_supportSet
    C rows n

theorem endpointReserveAugmentedRowWordCertificate_supports_disjoint_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  endpointReserveAugmentedRowWordCertificate_supports_disjoint C hrow

theorem endpointReserveAugmentedRowWordCertificate_evalsCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval leftRow)
      (C.toRowWordPlacementCertificate.eval rightRow) :=
  endpointReserveAugmentedRowWordCertificate_evalsCommute C hrow

theorem endpointReserveAugmentedRowWordCertificate_evalIteratesCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval leftRow)^[n])
      ((C.toRowWordPlacementCertificate.eval rightRow)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_evalIteratesCommute
    C hrow n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraRowSupportsDisjoint_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : ExtraRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraRowSupportsDisjoint
    C reserveRow extraRow

theorem endpointReserveAugmentedRowWordCertificate_extraReserveRowSupportsDisjoint_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) (reserveRow : Fin (2 * a + 3)) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveRowSupportsDisjoint
    C extraRow reserveRow

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalsCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : ExtraRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalsCommute
    C reserveRow extraRow

theorem endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalsCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) (reserveRow : Fin (2 * a + 3)) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalsCommute
    C extraRow reserveRow

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalIteratesCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : ExtraRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalIteratesCommute
    C reserveRow extraRow n k

theorem endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalIteratesCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) (reserveRow : Fin (2 * a + 3)) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[k]) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalIteratesCommute
    C extraRow reserveRow n k

theorem endpointReserveAugmentedRowWordCertificate_reserveEval_onReserve_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_reserveEval_onReserve
    C reserveRow

theorem endpointReserveAugmentedRowWordCertificate_extraEval_onExtra_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_extraEval_onExtra
    C extraRow

theorem endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
    C reserveRows

theorem endpointReserveAugmentedRowWordCertificate_extraWord_onExtra_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
    C extraRows

theorem endpointReserveAugmentedRowWordCertificate_reserveWordIter_onReserve_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (n : Nat) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n]) :=
  endpointReserveAugmentedRowWordCertificate_reserveWordIter_onReserve
    C reserveRows n

theorem endpointReserveAugmentedRowWordCertificate_extraWordIter_onExtra_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) (n : Nat) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n]) :=
  endpointReserveAugmentedRowWordCertificate_extraWordIter_onExtra
    C extraRows n

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordsCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (extraRows : List ExtraRow) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordsCommute
    C reserveRows extraRows

theorem endpointReserveAugmentedRowWordCertificate_extraReserveWordsCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) (reserveRows : List (Fin (2 * a + 3))) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveWordsCommute
    C extraRows reserveRows

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordItersCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (extraRows : List ExtraRow)
    (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordItersCommute
    C reserveRows extraRows n k

theorem endpointReserveAugmentedRowWordCertificate_extraReserveWordItersCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) (reserveRows : List (Fin (2 * a + 3)))
    (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveWordItersCommute
    C extraRows reserveRows n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint C

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint_symm_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint_symm C

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute C hf hg

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute_symm_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute_symm
    C hf hg

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute
    C hf hg n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute_symm_closed
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute_symm
    C hf hg n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute_closed
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute_symm_closed
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute_symm
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute_closed
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute_symm_closed
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute_symm
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedFinRowWordCertificate_extraPlacement_injective_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    Function.Injective C.extraPlacement :=
  endpointReserveAugmentedFinRowWordCertificate_extraPlacement_injective C

theorem endpointReserveAugmentedFinRowWordCertificate_supportSet_union_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedFinRowWordCertificate_supportSet_union C

theorem endpointReserveAugmentedFinRowWordCertificate_supportSet_iUnionRows_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) (Fin extraCount),
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  endpointReserveAugmentedFinRowWordCertificate_supportSet_iUnionRows C

theorem endpointReserveAugmentedFinRowWordCertificate_supportExtraProtected_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedFinRowWordCertificate_supportExtraProtected C

theorem endpointReserveAugmentedFinRowWordCertificate_supportExistsUniqueRow_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toSupportCertificate.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) (Fin extraCount),
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedFinRowWordCertificate_supportExistsUniqueRow C hx

theorem endpointReserveAugmentedFinRowWordCertificate_eval_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    C.toRowWordPlacementCertificate.eval row =
      wordEval (C.step row) (C.word row) :=
  endpointReserveAugmentedFinRowWordCertificate_eval C row

theorem endpointReserveAugmentedFinRowWordCertificate_eval_supported_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row)
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedFinRowWordCertificate_eval_supported C row

theorem endpointReserveAugmentedFinRowWordCertificate_step_supportedOn_supportSet_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount))
    (symbol : Symbol) :
    SupportedOn C.toSupportCertificate.supportSet (C.step row symbol) :=
  endpointReserveAugmentedFinRowWordCertificate_step_supportedOn_supportSet
    C row symbol

theorem endpointReserveAugmentedFinRowWordCertificate_eval_supportedOn_supportSet_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn C.toSupportCertificate.supportSet
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedFinRowWordCertificate_eval_supportedOn_supportSet
    C row

theorem endpointReserveAugmentedFinRowWordCertificate_evalWord_supportedOn_supportSet_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) :
    SupportedOn C.toSupportCertificate.supportSet
      (wordEval (fun row => C.toRowWordPlacementCertificate.eval row) rows) :=
  endpointReserveAugmentedFinRowWordCertificate_evalWord_supportedOn_supportSet
    C rows

theorem endpointReserveAugmentedFinRowWordCertificate_evalWord_iterate_supportedOn_supportSet_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) (n : Nat) :
    SupportedOn C.toSupportCertificate.supportSet
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval row) rows)^[n]) :=
  endpointReserveAugmentedFinRowWordCertificate_evalWord_iterate_supportedOn_supportSet
    C rows n

theorem endpointReserveAugmentedFinRowWordCertificate_supports_disjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  endpointReserveAugmentedFinRowWordCertificate_supports_disjoint C hrow

theorem endpointReserveAugmentedFinRowWordCertificate_evalsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval leftRow)
      (C.toRowWordPlacementCertificate.eval rightRow) :=
  endpointReserveAugmentedFinRowWordCertificate_evalsCommute C hrow

theorem endpointReserveAugmentedFinRowWordCertificate_evalIteratesCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval leftRow)^[n])
      ((C.toRowWordPlacementCertificate.eval rightRow)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_evalIteratesCommute
    C hrow n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowSupportsDisjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowSupportsDisjoint
    C reserveRow extraRow

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveRowSupportsDisjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveRowSupportsDisjoint
    C extraRow reserveRow

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalsCommute
    C reserveRow extraRow

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalsCommute
    C extraRow reserveRow

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalIteratesCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount)
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalIteratesCommute
    C reserveRow extraRow n k

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalIteratesCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3))
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalIteratesCommute
    C extraRow reserveRow n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveEval_onReserve_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveEval_onReserve
    C reserveRow

theorem endpointReserveAugmentedFinRowWordCertificate_extraEval_onExtra_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_extraEval_onExtra
    C extraRow

theorem endpointReserveAugmentedFinRowWordCertificate_reserveWord_onReserve_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveWord_onReserve
    C reserveRows

theorem endpointReserveAugmentedFinRowWordCertificate_extraWord_onExtra_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedFinRowWordCertificate_extraWord_onExtra
    C extraRows

theorem endpointReserveAugmentedFinRowWordCertificate_reserveWordIter_onReserve_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (n : Nat) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveWordIter_onReserve
    C reserveRows n

theorem endpointReserveAugmentedFinRowWordCertificate_extraWordIter_onExtra_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) (n : Nat) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n]) :=
  endpointReserveAugmentedFinRowWordCertificate_extraWordIter_onExtra
    C extraRows n

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordsCommute
    C reserveRows extraRows

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveWordsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveWordsCommute
    C extraRows reserveRows

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordItersCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordItersCommute
    C reserveRows extraRows n k

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveWordItersCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveWordItersCommute
    C extraRows reserveRows n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint C

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint_symm_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint_symm C

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute
    C hf hg

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute_symm_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute_symm
    C hf hg

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute
    C hf hg n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute_symm_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute_symm
    C hf hg n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute_symm_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute_symm
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute_symm_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute_symm
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_ne_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Fin extraCount} (hrow : leftRow ≠ rightRow) :
    C.extraPlacement leftRow ≠ C.extraPlacement rightRow :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_ne
    C hrow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_injective_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    Function.Injective C.extraPlacement :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_injective C

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_union_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_union C

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_iUnionRows_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) (Fin extraCount),
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_iUnionRows C

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportExtraProtected_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_supportExtraProtected C

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportExistsUniqueRow_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toSupportCertificate.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) (Fin extraCount),
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedCoordFinRowWordCertificate_supportExistsUniqueRow
    C hx

theorem endpointReserveAugmentedCoordFinRowWordCertificate_eval_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    C.toRowWordPlacementCertificate.eval row =
      wordEval (C.step row) (C.word row) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_eval C row

theorem endpointReserveAugmentedCoordFinRowWordCertificate_eval_supported_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row)
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_eval_supported C row

theorem endpointReserveAugmentedCoordFinRowWordCertificate_step_supportedOn_supportSet_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount))
    (symbol : Symbol) :
    SupportedOn C.toSupportCertificate.supportSet (C.step row symbol) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_step_supportedOn_supportSet
    C row symbol

theorem endpointReserveAugmentedCoordFinRowWordCertificate_eval_supportedOn_supportSet_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn C.toSupportCertificate.supportSet
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_eval_supportedOn_supportSet
    C row

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalWord_supportedOn_supportSet_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) :
    SupportedOn C.toSupportCertificate.supportSet
      (wordEval (fun row => C.toRowWordPlacementCertificate.eval row) rows) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_evalWord_supportedOn_supportSet
    C rows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalWordIter_supportedOn_support_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) (n : Nat) :
    SupportedOn C.toSupportCertificate.supportSet
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval row) rows)^[n]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_evalWordIter_supportedOn_support
    C rows n

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supports_disjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_supports_disjoint
    C hrow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval leftRow)
      (C.toRowWordPlacementCertificate.eval rightRow) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_evalsCommute C hrow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalIteratesCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval leftRow)^[n])
      ((C.toRowWordPlacementCertificate.eval rightRow)^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_evalIteratesCommute
    C hrow n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowSupportsDisjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow)) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowSupportsDisjoint
    C reserveRow extraRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowSupportsDisjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow)) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowSupportsDisjoint
    C extraRow reserveRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalsCommute
    C reserveRow extraRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalsCommute
    C extraRow reserveRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalIteratesCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount)
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalIteratesCommute
    C reserveRow extraRow n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalIteratesCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3))
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalIteratesCommute
    C extraRow reserveRow n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveEval_onReserve_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveEval_onReserve
    C reserveRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraEval_onExtra_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraEval_onExtra
    C extraRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveWord_onReserve_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveWord_onReserve
    C reserveRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraWord_onExtra_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraWord_onExtra
    C extraRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveWordIter_onReserve_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (n : Nat) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveWordIter_onReserve
    C reserveRows n

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraWordIter_onExtra_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) (n : Nat) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraWordIter_onExtra
    C extraRows n

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordsCommute
    C reserveRows extraRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordsCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordsCommute
    C extraRows reserveRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordItersCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordItersCommute
    C reserveRows extraRows n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordItersCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordItersCommute
    C extraRows reserveRows n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint C

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint_symm_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint_symm C

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute
    C hf hg

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute_symm_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute_symm
    C hf hg

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute
    C hf hg n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute_symm_closed
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute_symm
    C hf hg n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute_symm_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute_symm
    C leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute_symm_closed
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute_symm
    C leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReservePlacementCertificate_eval_supported_closed
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    (row : Fin (2 * a + 3)) :
    SupportedOn
      (rowPlacementSupport
        (endpointReservePlacement parent h a m ha hm) row)
      ((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval row) :=
  endpointReservePlacementCertificate_eval_supported
    parent h a m ha hm step word supported row

theorem endpointReservePlacementCertificate_supports_disjoint_closed
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    {leftRow rightRow : Fin (2 * a + 3)}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReservePlacement parent h a m ha hm) leftRow)
      (rowPlacementSupport
        (endpointReservePlacement parent h a m ha hm) rightRow) :=
  endpointReservePlacementCertificate_supports_disjoint
    parent h a m ha hm step word supported hrow

theorem endpointReservePlacementCertificate_evalsCommute_closed
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    {leftRow rightRow : Fin (2 * a + 3)}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      ((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval leftRow)
      ((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval rightRow) :=
  endpointReservePlacementCertificate_evalsCommute
    parent h a m ha hm step word supported hrow

theorem endpointReservePlacementCertificate_evalIteratesCommute_closed
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    {leftRow rightRow : Fin (2 * a + 3)}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      (((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval leftRow)^[n])
      (((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval rightRow)^[k]) :=
  endpointReservePlacementCertificate_evalIteratesCommute
    parent h a m ha hm step word supported hrow n k

theorem endpointReservePlacement_not_mem_protectedCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) (i : Fin (2 * a + 3)) :
    endpointReservePlacement parent h a m ha hm i ∉
      ProductCylinder T (PhaseProtectedStrips h (m ^ a)) :=
  endpointReservePlacement_not_mem_protectedCylinder
    parent h a m hh ha hm T i

theorem endpointReservePlacementSupport_eq_singleton_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i =
      ({endpointReservePlacement parent h a m ha hm i} :
        Set (Parent × PhaseSection h (m ^ a))) :=
  endpointReservePlacementSupport_eq_singleton parent h a m ha hm i

theorem endpointReservePlacementSupport_eq_productCylinder_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i =
      ProductCylinder ({parent} : Set Parent)
        ({(endpointReservePlacement parent h a m ha hm i).2} :
          Set (PhaseSection h (m ^ a))) :=
  endpointReservePlacementSupport_eq_productCylinder
    parent h a m ha hm i

theorem endpointReservePlacementSupports_disjoint_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j) :
    SetsDisjoint
      (rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i)
      (rowPlacementSupport (endpointReservePlacement parent h a m ha hm) j) :=
  endpointReservePlacementSupports_disjoint parent h a m ha hm hij

theorem endpointReservePlacementSupportedMapsCommute_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) rightMap) :
    Function.Commute leftMap rightMap :=
  endpointReservePlacementSupportedMapsCommute
    parent h a m ha hm hij hleft hright

theorem endpointReservePlacementSupportedMapsCommute_symm_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) rightMap) :
    Function.Commute leftMap rightMap :=
  endpointReservePlacementSupportedMapsCommute_symm
    parent h a m ha hm hij hleft hright

theorem endpointReservePlacementSupportedIteratesCommute_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  endpointReservePlacementSupportedIteratesCommute
    parent h a m ha hm hij hleft hright n k

theorem endpointReservePlacementSupportedIteratesCommute_symm_closed
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  endpointReservePlacementSupportedIteratesCommute_symm
    parent h a m ha hm hij hleft hright n k

theorem endpointReservePlacementSupportedWordEvalsCommute_closed
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReservePlacementSupportedWordEvalsCommute
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord

theorem endpointReservePlacementSupportedWordEvalsCommute_symm_closed
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReservePlacementSupportedWordEvalsCommute_symm
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord

theorem endpointReservePlacementSupportedWordEvalIteratesCommute_closed
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReservePlacementSupportedWordEvalIteratesCommute
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord n k

theorem endpointReservePlacementSupportedWordEvalIteratesCommute_symm_closed
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReservePlacementSupportedWordEvalIteratesCommute_symm
    parent h a m ha hm hij leftStep rightStep hleft hright
    leftWord rightWord n k

theorem terminalWord4_closed :
    terminalWord4 = [TerminalSymbol.F1, TerminalSymbol.F0, TerminalSymbol.F0] :=
  rfl

theorem terminalWord6_closed :
    terminalWord6 =
      [TerminalSymbol.F1, TerminalSymbol.F1,
       TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0] :=
  rfl

theorem terminalTrace4_closed :
    terminalTrace4 = [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F1] :=
  rfl

theorem terminalTrace6_closed :
    terminalTrace6 =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0,
       TerminalSymbol.F1, TerminalSymbol.F1] :=
  rfl

theorem terminalResetWord4_closed :
    terminalResetWord4 =
      [TerminalSymbol.F1, TerminalSymbol.F2, TerminalSymbol.F0] :=
  rfl

theorem terminalResetTrace4_closed :
    terminalResetTrace4 =
      [TerminalSymbol.F0, TerminalSymbol.F2, TerminalSymbol.F1] :=
  rfl

theorem terminalWord4_length_closed :
    terminalWord4.length = 3 :=
  terminalWord4_length

theorem terminalWord6_length_closed :
    terminalWord6.length = 5 :=
  terminalWord6_length

theorem terminalTrace4_length_closed :
    terminalTrace4.length = 3 :=
  terminalTrace4_length

theorem terminalTrace6_length_closed :
    terminalTrace6.length = 5 :=
  terminalTrace6_length

theorem terminalResetWord4_length_closed :
    terminalResetWord4.length = 3 :=
  terminalResetWord4_length

theorem terminalResetTrace4_length_closed :
    terminalResetTrace4.length = 3 :=
  terminalResetTrace4_length

theorem terminalWord4_eval_closed
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalWord4 x =
      F TerminalSymbol.F0
        (F TerminalSymbol.F0
          (F TerminalSymbol.F1 x)) :=
  terminalWord4_eval F x

theorem terminalWord6_eval_closed
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalWord6 x =
      F TerminalSymbol.F0
        (F TerminalSymbol.F0
          (F TerminalSymbol.F0
            (F TerminalSymbol.F1
              (F TerminalSymbol.F1 x)))) :=
  terminalWord6_eval F x

theorem terminalTrace4_eval_closed
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalTrace4 x =
      F TerminalSymbol.F1
        (F TerminalSymbol.F0
          (F TerminalSymbol.F0 x)) :=
  terminalTrace4_eval F x

theorem terminalTrace6_eval_closed
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalTrace6 x =
      F TerminalSymbol.F1
        (F TerminalSymbol.F1
          (F TerminalSymbol.F0
            (F TerminalSymbol.F0
              (F TerminalSymbol.F0 x)))) :=
  terminalTrace6_eval F x

theorem terminalResetWord4_eval_closed
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalResetWord4 x =
      F TerminalSymbol.F0
        (F TerminalSymbol.F2
          (F TerminalSymbol.F1 x)) :=
  terminalResetWord4_eval F x

theorem terminalResetTrace4_eval_closed
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalResetTrace4 x =
      F TerminalSymbol.F1
        (F TerminalSymbol.F2
          (F TerminalSymbol.F0 x)) :=
  terminalResetTrace4_eval F x

theorem rankCycleCertificate_singleCycle_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : RankCycleCertificate α N) :
    Shared.IsSingleCycleMap C.step :=
  rankCycleCertificate_singleCycle C

theorem rankCycleCertificate_iterate_rank_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : RankCycleCertificate α N) (n : Nat) (x : α) :
    C.rank ((C.step^[n]) x) = C.rank x + (n : ZMod N) :=
  rankCycleCertificate_iterate_rank C n x

theorem indexedOrbitCertificate_singleCycle_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) :
    Shared.IsSingleCycleMap C.step :=
  indexedOrbitCertificate_singleCycle C

theorem indexedOrbitCertificate_rankStep_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (x : α) :
    C.toCycleCoordinate.equiv.symm (C.step x) =
      C.toCycleCoordinate.equiv.symm x + 1 :=
  indexedOrbitCertificate_rankStep C x

theorem indexedOrbitCertificate_iterate_rank_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (n : Nat) (x : α) :
    C.toCycleCoordinate.equiv.symm ((C.step^[n]) x) =
      C.toCycleCoordinate.equiv.symm x + (n : ZMod N) :=
  indexedOrbitCertificate_iterate_rank C n x

theorem indexedOrbitCertificate_iterate_orbit_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (i : Fin N) (n : Nat) :
    (C.step^[n]) (C.orbit i) = C.orbit (i + Fin.ofNat N n) :=
  indexedOrbitCertificate_iterate_orbit C i n

theorem indexedOrbitCertificate_coordinate_orbit_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (i : Fin N) :
    C.orbit.symm (C.orbit i) = i :=
  indexedOrbitCertificate_coordinate_orbit C i

theorem indexedOrbitCertificate_coordinate_iterate_orbit_closed
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (i : Fin N) (n : Nat) :
    C.orbit.symm ((C.step^[n]) (C.orbit i)) =
      i + Fin.ofNat N n :=
  indexedOrbitCertificate_coordinate_iterate_orbit C i n

theorem wordRankCycleCertificate_singleCycle_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : WordRankCycleCertificate ι α N) :
    Shared.IsSingleCycleMap (wordEval C.symbolStep C.word) :=
  wordRankCycleCertificate_singleCycle C

theorem wordRankCycleCertificate_iterate_rank_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : WordRankCycleCertificate ι α N) (n : Nat) (x : α) :
    C.rank (((wordEval C.symbolStep C.word)^[n]) x) =
      C.rank x + (n : ZMod N) :=
  wordRankCycleCertificate_iterate_rank C n x

theorem indexedWordOrbitCertificate_singleCycle_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) :
    Shared.IsSingleCycleMap (wordEval C.symbolStep C.word) :=
  indexedWordOrbitCertificate_singleCycle C

theorem indexedWordOrbitCertificate_rankStep_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (x : α) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (wordEval C.symbolStep C.word x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x + 1 :=
  indexedWordOrbitCertificate_rankStep C x

theorem indexedWordOrbitCertificate_iterate_rank_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (n : Nat) (x : α) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (((wordEval C.symbolStep C.word)^[n]) x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x +
        (n : ZMod N) :=
  indexedWordOrbitCertificate_iterate_rank C n x

theorem indexedWordOrbitCertificate_iterate_orbit_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (i : Fin N) (n : Nat) :
    ((wordEval C.symbolStep C.word)^[n]) (C.orbit i) =
      C.orbit (i + Fin.ofNat N n) :=
  indexedWordOrbitCertificate_iterate_orbit C i n

theorem indexedWordOrbitCertificate_coordinate_orbit_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (i : Fin N) :
    C.orbit.symm (C.orbit i) = i :=
  indexedWordOrbitCertificate_coordinate_orbit C i

theorem indexedWordOrbitCertificate_coordinate_iterate_orbit_closed
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (i : Fin N) (n : Nat) :
    C.orbit.symm (((wordEval C.symbolStep C.word)^[n]) (C.orbit i)) =
      i + Fin.ofNat N n :=
  indexedWordOrbitCertificate_coordinate_iterate_orbit C i n

theorem wordSkewRankCycleCertificate_singleCycle_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : WordSkewRankCycleCertificate Symbol Base Fiber N) :
    Shared.IsSingleCycleMap
      (wordSkewEval C.baseStep C.fiberStep C.word) :=
  wordSkewRankCycleCertificate_singleCycle C

theorem wordSkewRankCycleCertificate_iterate_rank_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : WordSkewRankCycleCertificate Symbol Base Fiber N)
    (n : Nat) (x : Base × Fiber) :
    C.rank (((wordSkewEval C.baseStep C.fiberStep C.word)^[n]) x) =
      C.rank x + (n : ZMod N) :=
  wordSkewRankCycleCertificate_iterate_rank C n x

theorem indexedWordSkewOrbitCertificate_singleCycle_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N) :
    Shared.IsSingleCycleMap (wordSkewEval C.baseStep C.fiberStep C.word) :=
  indexedWordSkewOrbitCertificate_singleCycle C

theorem indexedWordSkewOrbitCertificate_rankStep_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N)
    (x : Base × Fiber) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (wordSkewEval C.baseStep C.fiberStep C.word x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x + 1 :=
  indexedWordSkewOrbitCertificate_rankStep C x

theorem indexedWordSkewOrbitCertificate_iterate_rank_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N)
    (n : Nat) (x : Base × Fiber) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (((wordSkewEval C.baseStep C.fiberStep C.word)^[n]) x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x +
        (n : ZMod N) :=
  indexedWordSkewOrbitCertificate_iterate_rank C n x

theorem indexedWordSkewOrbitCertificate_iterate_orbit_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N)
    (i : Fin N) (n : Nat) :
    ((wordSkewEval C.baseStep C.fiberStep C.word)^[n])
        (C.orbit i) =
      C.orbit (i + Fin.ofNat N n) :=
  indexedWordSkewOrbitCertificate_iterate_orbit C i n

theorem indexedWordSkewOrbitCertificate_coordinate_orbit_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N) (i : Fin N) :
    C.orbit.symm (C.orbit i) = i :=
  indexedWordSkewOrbitCertificate_coordinate_orbit C i

theorem indexedWordSkewOrbitCertificate_coordinate_iterate_orbit_closed
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N)
    (i : Fin N) (n : Nat) :
    C.orbit.symm
        (((wordSkewEval C.baseStep C.fiberStep C.word)^[n])
          (C.orbit i)) =
      i + Fin.ofNat N n :=
  indexedWordSkewOrbitCertificate_coordinate_iterate_orbit C i n

theorem terminalQ_card_closed
    (m : Nat) [NeZero m] :
    Fintype.card (TerminalQ m) = m * m :=
  terminalQ_card m

theorem terminalQ_complementExponentSum_closed
    {m M : Nat} [NeZero m] (q0 : TerminalQ m) :
    (∑ q : TerminalQ m, if q = q0 then (0 : ZMod M) else 1) =
      ((m * m - 1 : Nat) : ZMod M) :=
  terminalQ_complementExponentSum q0

theorem terminalQComplementProductExponentSingleCycle_closed
    {N m k : Nat} [NeZero N] [NeZero m]
    (terminalStep : TerminalQ m → TerminalQ m)
    (terminalRank : TerminalQ m ≃ ZMod N)
    (base q0 : TerminalQ m)
    (hstep : ∀ q : TerminalQ m,
      terminalRank (terminalStep q) = terminalRank q + 1) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (fun q : TerminalQ m =>
          if q = q0 then (0 : ZMod (m ^ k)) else 1)) :=
  terminalQComplementProductExponentSingleCycle terminalStep
    terminalRank base q0 hstep

theorem terminalTrace4_singleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4) :=
  terminalTrace4_singleCycle

theorem terminalOrbit4_bijective_closed :
    Function.Bijective terminalOrbit4 :=
  terminalOrbit4_bijective

theorem terminalTrace4_stepOrbit_closed :
    ∀ i : Fin 16,
      terminalOrbit4Equiv (i + 1) =
        wordEval (terminalSymbolStep 4) terminalTrace4
          (terminalOrbit4Equiv i) :=
  terminalTrace4_stepOrbit

theorem terminalTrace4_iterate_orbit_closed
    (i : Fin 16) :
    ∀ n : Nat,
      ((wordEval (terminalSymbolStep 4) terminalTrace4)^[n])
          (terminalOrbit4Equiv i) =
        terminalOrbit4Equiv (i + Fin.ofNat 16 n) :=
  terminalTrace4_iterate_orbit i

theorem terminalTrace4_coordinate_orbit_closed
    (i : Fin 16) :
    terminalOrbit4Equiv.symm (terminalOrbit4Equiv i) = i :=
  terminalTrace4_coordinate_orbit i

theorem terminalTrace4_coordinate_iterate_orbit_closed
    (i : Fin 16) (n : Nat) :
    terminalOrbit4Equiv.symm
        (((wordEval (terminalSymbolStep 4) terminalTrace4)^[n])
          (terminalOrbit4Equiv i)) =
      i + Fin.ofNat 16 n :=
  terminalTrace4_coordinate_iterate_orbit i n

theorem terminalTrace6_singleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6) :=
  terminalTrace6_singleCycle

theorem terminalResetTrace4_singleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  terminalResetTrace4_singleCycle

theorem terminalResetOrbit4_bijective_closed :
    Function.Bijective terminalResetOrbit4 :=
  terminalResetOrbit4_bijective

theorem terminalResetTrace4_stepOrbit_closed :
    ∀ i : Fin 16,
      terminalResetOrbit4Equiv (i + 1) =
        wordEval (terminalSymbolStep 4) terminalResetTrace4
          (terminalResetOrbit4Equiv i) :=
  terminalResetTrace4_stepOrbit

theorem d54TerminalSelector_nodup_closed :
    d54TerminalSelector.Nodup :=
  d54TerminalSelector_nodup

theorem d54TerminalResetSites_nodup_closed :
    d54TerminalResetSites.Nodup :=
  d54TerminalResetSites_nodup

theorem d54TerminalResetSites_disjoint_selector_closed :
    listsDisjoint d54TerminalResetSites d54TerminalSelector :=
  d54TerminalResetSites_disjoint_selector

theorem d54FinalCylinders_nodup_closed :
    d54FinalCylinders.Nodup :=
  d54FinalCylinders_nodup

theorem d54FinalCylinders_avoid_liftedSelector_closed :
    cylindersAvoidPoints d54FinalCylinders d54LiftedSelector :=
  d54FinalCylinders_avoid_liftedSelector

theorem d54ReservePoints_nodup_closed :
    d54ReservePoints.Nodup :=
  d54ReservePoints_nodup

theorem d54ReservePoints_count_closed :
    d54ReservePoints.length = 8 :=
  d54ReservePoints_count

theorem d54ReservePoints_avoid_finalCylinders_closed :
    reservesAvoidCylinders reservePoints d54FinalCylinders :=
  d54ReservePoints_avoid_finalCylinders

theorem d54ReservePoints_disjoint_liftedSelector_closed :
    listsDisjoint reservePoints d54LiftedSelector :=
  d54ReservePoints_disjoint_liftedSelector

theorem d54ResetTableCertificate_terminalOrbitBijective_closed :
    Function.Bijective terminalResetOrbit4 :=
  d54ResetTableCertificate_terminalOrbitBijective

theorem d54ResetTableCertificate_terminalStepOrbit_closed :
    ∀ i : Fin 16,
      terminalResetOrbit4Equiv (i + 1) =
        wordEval (terminalSymbolStep 4) terminalResetTrace4
          (terminalResetOrbit4Equiv i) :=
  d54ResetTableCertificate_terminalStepOrbit

theorem d54ResetTableCertificate_terminalSingleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  d54ResetTableCertificate_terminalSingleCycle

theorem d54ResetTableCertificate_selectorNodup_closed :
    d54TerminalSelector.Nodup :=
  d54ResetTableCertificate_selectorNodup

theorem d54ResetTableCertificate_resetSitesNodup_closed :
    d54TerminalResetSites.Nodup :=
  d54ResetTableCertificate_resetSitesNodup

theorem d54ResetTableCertificate_resetSitesDisjointSelector_closed :
    listsDisjoint d54TerminalResetSites d54TerminalSelector :=
  d54ResetTableCertificate_resetSitesDisjointSelector

theorem d54ResetTableCertificate_finalCylindersNodup_closed :
    d54FinalCylinders.Nodup :=
  d54ResetTableCertificate_finalCylindersNodup

theorem d54ResetTableCertificate_finalCylindersAvoidLiftedSelector_closed :
    cylindersAvoidPoints d54FinalCylinders d54LiftedSelector :=
  d54ResetTableCertificate_finalCylindersAvoidLiftedSelector

theorem d54ResetTableCertificate_reservePointsNodup_closed :
    d54ReservePoints.Nodup :=
  d54ResetTableCertificate_reservePointsNodup

theorem d54ResetTableCertificate_reservePointsCount_closed :
    d54ReservePoints.length = 8 :=
  d54ResetTableCertificate_reservePointsCount

theorem d54ResetTableCertificate_reservePointsAvoidFinalCylinders_closed :
    reservesAvoidCylinders reservePoints d54FinalCylinders :=
  d54ResetTableCertificate_reservePointsAvoidFinalCylinders

theorem d54ResetTableCertificate_reservePointsDisjointLiftedSelector_closed :
    listsDisjoint reservePoints d54LiftedSelector :=
  d54ResetTableCertificate_reservePointsDisjointLiftedSelector

theorem foldedSites4_codes_closed :
    allCodesMatch (m := 4) foldedSites4 :=
  foldedSites4_codes

theorem foldedSites6_codes_closed :
    allCodesMatch (m := 6) foldedSites6 :=
  foldedSites6_codes

theorem foldedSites4_length_closed :
    foldedSites4.length = 7 :=
  foldedSites4_length

theorem foldedSites6_length_closed :
    foldedSites6.length = 7 :=
  foldedSites6_length

theorem foldedSites4_roles_closed :
    foldedSiteRoles foldedSites4 = foldedRoleTable :=
  foldedSites4_roles

theorem foldedSites6_roles_closed :
    foldedSiteRoles foldedSites6 = foldedRoleTable :=
  foldedSites6_roles

theorem foldedSites4_roles_nodup_closed :
    (foldedSiteRoles foldedSites4).Nodup :=
  foldedSites4_roles_nodup

theorem foldedSites6_roles_nodup_closed :
    (foldedSiteRoles foldedSites6).Nodup :=
  foldedSites6_roles_nodup

theorem foldedSites4_codeList_closed :
    foldedSiteCodes foldedSites4 = [0, 16, 1092, 128, 144, 32, 96] :=
  foldedSites4_codeList

theorem foldedSites6_codeList_closed :
    foldedSiteCodes foldedSites6 = [0, 36, 1014, 324, 1224, 792, 288] :=
  foldedSites6_codeList

theorem foldedSites4_hits_closed :
    foldedSiteHits foldedSites4 =
      [ ⟨1, TerminalSymbol.F0⟩,
        ⟨3, TerminalSymbol.F1⟩,
        ⟨2, TerminalSymbol.F0⟩ ] :=
  foldedSites4_hits

theorem foldedSites6_hits_closed :
    foldedSiteHits foldedSites6 =
      [ ⟨1, TerminalSymbol.F0⟩,
        ⟨4, TerminalSymbol.F1⟩,
        ⟨2, TerminalSymbol.F0⟩,
        ⟨3, TerminalSymbol.F0⟩,
        ⟨5, TerminalSymbol.F1⟩ ] :=
  foldedSites6_hits

theorem foldedSites4_hitSymbolsAt_zero_closed :
    hitSymbolsAt 0 foldedSites4 = [] :=
  foldedSites4_hitSymbolsAt_zero

theorem foldedSites4_hitSymbolsAt_one_closed :
    hitSymbolsAt 1 foldedSites4 = [TerminalSymbol.F0] :=
  foldedSites4_hitSymbolsAt_one

theorem foldedSites4_hitSymbolsAt_two_closed :
    hitSymbolsAt 2 foldedSites4 = [TerminalSymbol.F0] :=
  foldedSites4_hitSymbolsAt_two

theorem foldedSites4_hitSymbolsAt_three_closed :
    hitSymbolsAt 3 foldedSites4 = [TerminalSymbol.F1] :=
  foldedSites4_hitSymbolsAt_three

theorem foldedSites6_hitSymbolsAt_zero_closed :
    hitSymbolsAt 0 foldedSites6 = [] :=
  foldedSites6_hitSymbolsAt_zero

theorem foldedSites6_hitSymbolsAt_one_closed :
    hitSymbolsAt 1 foldedSites6 = [TerminalSymbol.F0] :=
  foldedSites6_hitSymbolsAt_one

theorem foldedSites6_hitSymbolsAt_two_closed :
    hitSymbolsAt 2 foldedSites6 = [TerminalSymbol.F0] :=
  foldedSites6_hitSymbolsAt_two

theorem foldedSites6_hitSymbolsAt_three_closed :
    hitSymbolsAt 3 foldedSites6 = [TerminalSymbol.F0] :=
  foldedSites6_hitSymbolsAt_three

theorem foldedSites6_hitSymbolsAt_four_closed :
    hitSymbolsAt 4 foldedSites6 = [TerminalSymbol.F1] :=
  foldedSites6_hitSymbolsAt_four

theorem foldedSites6_hitSymbolsAt_five_closed :
    hitSymbolsAt 5 foldedSites6 = [TerminalSymbol.F1] :=
  foldedSites6_hitSymbolsAt_five

theorem foldedSites4_chronologicalTrace_by_slots_closed :
    chronologicalTrace 4 foldedSites4 =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F1] :=
  foldedSites4_chronologicalTrace_by_slots

theorem foldedSites6_chronologicalTrace_by_slots_closed :
    chronologicalTrace 6 foldedSites6 =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0,
        TerminalSymbol.F1, TerminalSymbol.F1] :=
  foldedSites6_chronologicalTrace_by_slots

theorem foldedSites4_chronologicalTrace_closed :
    chronologicalTrace 4 foldedSites4 = terminalTrace4 :=
  foldedSites4_chronologicalTrace

theorem foldedSites6_chronologicalTrace_closed :
    chronologicalTrace 6 foldedSites6 = terminalTrace6 :=
  foldedSites6_chronologicalTrace

theorem foldedSites4_singleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (chronologicalTrace 4 foldedSites4)) :=
  foldedSites4_singleCycle

theorem foldedSites6_singleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (chronologicalTrace 6 foldedSites6)) :=
  foldedSites6_singleCycle

theorem protected4_codes_closed :
    allCodedCoordsMatch protected4 :=
  protected4_codes

theorem protected6_codes_closed :
    allCodedCoordsMatch protected6 :=
  protected6_codes

theorem reserves4_codes_closed :
    allReserveCodesMatch reserves4 :=
  reserves4_codes

theorem reserves6_codes_closed :
    allReserveCodesMatch reserves6 :=
  reserves6_codes

theorem protected4_length_closed :
    protected4.length = 4 :=
  protected4_length

theorem protected6_length_closed :
    protected6.length = 4 :=
  protected6_length

theorem reserves4_length_closed :
    reserves4.length = 10 :=
  reserves4_length

theorem reserves6_length_closed :
    reserves6.length = 10 :=
  reserves6_length

theorem protected4_codeList_closed :
    codedCoordCodes protected4 = [68, 886, 1352, 3143] :=
  protected4_codeList

theorem protected6_codeList_closed :
    codedCoordCodes protected6 = [2910, 10908, 41532, 42623] :=
  protected6_codeList

theorem protected4_nodup_closed :
    (codedCoords protected4).Nodup :=
  protected4_nodup

theorem protected6_nodup_closed :
    (codedCoords protected6).Nodup :=
  protected6_nodup

theorem reserves4_roles_closed :
    reserveRoles reserves4 = reserveRoleTable :=
  reserves4_roles

theorem reserves6_roles_closed :
    reserveRoles reserves6 = reserveRoleTable :=
  reserves6_roles

theorem reserves4_roles_nodup_closed :
    (reserveRoles reserves4).Nodup :=
  reserves4_roles_nodup

theorem reserves6_roles_nodup_closed :
    (reserveRoles reserves6).Nodup :=
  reserves6_roles_nodup

theorem reserves4_codeList_closed :
    reserveStateCodes reserves4 =
      [240, 241, 242, 243, 244, 245, 246, 247, 248, 249] :=
  reserves4_codeList

theorem reserves6_codeList_closed :
    reserveStateCodes reserves6 =
      [1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268,
        1269] :=
  reserves6_codeList

theorem protected4_qzSeparatedFromSites_closed :
    qzSeparatedFromSites (codedCoords protected4) foldedSites4 :=
  protected4_qzSeparatedFromSites

theorem protected6_qzSeparatedFromSites_closed :
    qzSeparatedFromSites (codedCoords protected6) foldedSites6 :=
  protected6_qzSeparatedFromSites

theorem reserves4_nodup_closed :
    (reserveCoords reserves4).Nodup :=
  reserves4_nodup

theorem reserves6_nodup_closed :
    (reserveCoords reserves6).Nodup :=
  reserves6_nodup

theorem reserves4_terminalProjection_closed :
    allQProjection ((3 : ZMod 4), (3 : ZMod 4))
      (reserveCoords reserves4) :=
  reserves4_terminalProjection

theorem reserves6_terminalProjection_closed :
    allQProjection ((5 : ZMod 6), (5 : ZMod 6))
      (reserveCoords reserves6) :=
  reserves6_terminalProjection

theorem reserveProjection4_absent_from_sites_closed :
    qProjectionAbsent ((3 : ZMod 4), (3 : ZMod 4))
      (siteCoords foldedSites4) :=
  reserveProjection4_absent_from_sites

theorem reserveProjection6_absent_from_sites_closed :
    qProjectionAbsent ((5 : ZMod 6), (5 : ZMod 6))
      (siteCoords foldedSites6) :=
  reserveProjection6_absent_from_sites

theorem reserveProjection4_absent_from_protected_closed :
    qProjectionAbsent ((3 : ZMod 4), (3 : ZMod 4))
      (codedCoords protected4) :=
  reserveProjection4_absent_from_protected

theorem reserveProjection6_absent_from_protected_closed :
    qProjectionAbsent ((5 : ZMod 6), (5 : ZMod 6))
      (codedCoords protected6) :=
  reserveProjection6_absent_from_protected

theorem singletonCommonEdgeWitness4_colors_closed :
    singletonCommonEdgeWitness4.colors = { first := 0, second := 1 } :=
  singletonCommonEdgeWitness4_colors

theorem singletonCommonEdgeWitness6_colors_closed :
    singletonCommonEdgeWitness6.colors = { first := 2, second := 5 } :=
  singletonCommonEdgeWitness6_colors

theorem singletonCommonEdgeWitness4_selectorCode_closed :
    singletonCommonEdgeWitness4.selector.code = 68 :=
  singletonCommonEdgeWitness4_selectorCode

theorem singletonCommonEdgeWitness6_selectorCode_closed :
    singletonCommonEdgeWitness6.selector.code = 2910 :=
  singletonCommonEdgeWitness6_selectorCode

theorem singletonCommonEdgeWitness4_commonImageCode_closed :
    singletonCommonEdgeWitness4.commonImage.code = 1352 :=
  singletonCommonEdgeWitness4_commonImageCode

theorem singletonCommonEdgeWitness6_commonImageCode_closed :
    singletonCommonEdgeWitness6.commonImage.code = 10908 :=
  singletonCommonEdgeWitness6_commonImageCode

theorem singletonCommonEdgeWitness4_selectorCodeMatches_closed :
    codedCoordMatches singletonCommonEdgeWitness4.selector = true :=
  singletonCommonEdgeWitness4_selectorCodeMatches

theorem singletonCommonEdgeWitness6_selectorCodeMatches_closed :
    codedCoordMatches singletonCommonEdgeWitness6.selector = true :=
  singletonCommonEdgeWitness6_selectorCodeMatches

theorem singletonCommonEdgeWitness4_commonImageCodeMatches_closed :
    codedCoordMatches singletonCommonEdgeWitness4.commonImage = true :=
  singletonCommonEdgeWitness4_commonImageCodeMatches

theorem singletonCommonEdgeWitness6_commonImageCodeMatches_closed :
    codedCoordMatches singletonCommonEdgeWitness6.commonImage = true :=
  singletonCommonEdgeWitness6_commonImageCodeMatches

theorem singletonCommonEdgeWitness4_protected_closed :
    singletonCommonEdgeWitness4.protectedSet = protected4 :=
  singletonCommonEdgeWitness4_protected

theorem singletonCommonEdgeWitness6_protected_closed :
    singletonCommonEdgeWitness6.protectedSet = protected6 :=
  singletonCommonEdgeWitness6_protected

theorem singletonCommonEdgeWitness4_protectedSize_closed :
    singletonCommonEdgeWitness4.protectedSet.length = singletonCommonEdgeWitness4.protectedSize :=
  singletonCommonEdgeWitness4_protectedSize

theorem singletonCommonEdgeWitness6_protectedSize_closed :
    singletonCommonEdgeWitness6.protectedSet.length = singletonCommonEdgeWitness6.protectedSize :=
  singletonCommonEdgeWitness6_protectedSize

theorem singletonCommonEdgeWitness4_protected_nodup_closed :
    (codedCoords singletonCommonEdgeWitness4.protectedSet).Nodup :=
  singletonCommonEdgeWitness4_protected_nodup

theorem singletonCommonEdgeWitness6_protected_nodup_closed :
    (codedCoords singletonCommonEdgeWitness6.protectedSet).Nodup :=
  singletonCommonEdgeWitness6_protected_nodup

theorem singletonCommonEdgeWitness4_selector_mem_protected_closed :
    singletonCommonEdgeWitness4.selector ∈ singletonCommonEdgeWitness4.protectedSet :=
  singletonCommonEdgeWitness4_selector_mem_protected

theorem singletonCommonEdgeWitness6_selector_mem_protected_closed :
    singletonCommonEdgeWitness6.selector ∈ singletonCommonEdgeWitness6.protectedSet :=
  singletonCommonEdgeWitness6_selector_mem_protected

theorem singletonCommonEdgeWitness4_commonImage_mem_protected_closed :
    singletonCommonEdgeWitness4.commonImage ∈ singletonCommonEdgeWitness4.protectedSet :=
  singletonCommonEdgeWitness4_commonImage_mem_protected

theorem singletonCommonEdgeWitness6_commonImage_mem_protected_closed :
    singletonCommonEdgeWitness6.commonImage ∈ singletonCommonEdgeWitness6.protectedSet :=
  singletonCommonEdgeWitness6_commonImage_mem_protected

theorem singletonCommonEdgeWitness4_selector_ne_commonImage_closed :
    singletonCommonEdgeWitness4.selector ≠
      singletonCommonEdgeWitness4.commonImage :=
  singletonCommonEdgeWitness4_selector_ne_commonImage

theorem singletonCommonEdgeWitness6_selector_ne_commonImage_closed :
    singletonCommonEdgeWitness6.selector ≠
      singletonCommonEdgeWitness6.commonImage :=
  singletonCommonEdgeWitness6_selector_ne_commonImage

theorem singletonCommonEdgeWitness4_terminalTrace_closed :
    singletonCommonEdgeWitness4.terminalTrace = terminalTrace4 :=
  singletonCommonEdgeWitness4_terminalTrace

theorem singletonCommonEdgeWitness6_terminalTrace_closed :
    singletonCommonEdgeWitness6.terminalTrace = terminalTrace6 :=
  singletonCommonEdgeWitness6_terminalTrace

theorem singletonCommonEdgeWitness4_terminalTrace_eq_foldedSites_closed :
    singletonCommonEdgeWitness4.terminalTrace =
      chronologicalTrace 4 foldedSites4 :=
  singletonCommonEdgeWitness4_terminalTrace_eq_foldedSites

theorem singletonCommonEdgeWitness6_terminalTrace_eq_foldedSites_closed :
    singletonCommonEdgeWitness6.terminalTrace =
      chronologicalTrace 6 foldedSites6 :=
  singletonCommonEdgeWitness6_terminalTrace_eq_foldedSites

theorem singletonCommonEdgeWitness4_terminalTrace_by_slots_closed :
    singletonCommonEdgeWitness4.terminalTrace =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F1] :=
  singletonCommonEdgeWitness4_terminalTrace_by_slots

theorem singletonCommonEdgeWitness6_terminalTrace_by_slots_closed :
    singletonCommonEdgeWitness6.terminalTrace =
      [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0,
        TerminalSymbol.F1, TerminalSymbol.F1] :=
  singletonCommonEdgeWitness6_terminalTrace_by_slots

theorem singletonCommonEdgeWitness4_traceSingleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) singletonCommonEdgeWitness4.terminalTrace) :=
  singletonCommonEdgeWitness4_traceSingleCycle

theorem singletonCommonEdgeWitness6_traceSingleCycle_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) singletonCommonEdgeWitness6.terminalTrace) :=
  singletonCommonEdgeWitness6_traceSingleCycle

theorem singletonCommonEdgeWitness4_traceSingleCycle_fromFoldedSites_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) singletonCommonEdgeWitness4.terminalTrace) :=
  singletonCommonEdgeWitness4_traceSingleCycle_fromFoldedSites

theorem singletonCommonEdgeWitness6_traceSingleCycle_fromFoldedSites_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) singletonCommonEdgeWitness6.terminalTrace) :=
  singletonCommonEdgeWitness6_traceSingleCycle_fromFoldedSites

theorem singletonCommonEdgeWitness4_traceSingleCycle_fromSlots_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) singletonCommonEdgeWitness4.terminalTrace) :=
  singletonCommonEdgeWitness4_traceSingleCycle_fromSlots

theorem singletonCommonEdgeWitness6_traceSingleCycle_fromSlots_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) singletonCommonEdgeWitness6.terminalTrace) :=
  singletonCommonEdgeWitness6_traceSingleCycle_fromSlots

theorem singletonCommonEdgeWitness4_protectedSeparatedFromSites_closed :
    qzSeparatedFromSites (codedCoords singletonCommonEdgeWitness4.protectedSet) foldedSites4 :=
  singletonCommonEdgeWitness4_protectedSeparatedFromSites

theorem singletonCommonEdgeWitness6_protectedSeparatedFromSites_closed :
    qzSeparatedFromSites (codedCoords singletonCommonEdgeWitness6.protectedSet) foldedSites6 :=
  singletonCommonEdgeWitness6_protectedSeparatedFromSites

theorem foldedEndpointMarkedTransferInput4_holds_closed :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput4 :=
  foldedEndpointMarkedTransferInput4_holds

theorem foldedEndpointMarkedTransferInput6_holds_closed :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput6 :=
  foldedEndpointMarkedTransferInput6_holds

theorem foldedEndpointMarkedTransferInputAudit_holds_closed :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit :=
  foldedEndpointMarkedTransferInputAudit_holds

theorem chainDescendantCut_parent_closed
    {n : Nat} (cut edge : Fin n) :
    chainDescendantCut cut (chainParent edge) ↔ cut.val < edge.val :=
  chainDescendantCut_parent cut edge

theorem chainDescendantCut_child_closed
    {n : Nat} (cut edge : Fin n) :
    chainDescendantCut cut (chainChild edge) ↔ cut.val ≤ edge.val :=
  chainDescendantCut_child cut edge

theorem chainIncidence_eq_ite_closed
    {n : Nat} (cut edge : Fin n) :
    chainIncidence cut edge = if cut = edge then (1 : Int) else 0 :=
  chainIncidence_eq_ite cut edge

theorem chainIncidence_self_closed
    {n : Nat} (edge : Fin n) :
    chainIncidence edge edge = 1 :=
  chainIncidence_self edge

theorem chainIncidence_ne_closed
    {n : Nat} {cut edge : Fin n} (hne : cut ≠ edge) :
    chainIncidence cut edge = 0 :=
  chainIncidence_ne hne

theorem parentMapIncidence_eq_ite_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex)
    (hboundary : ParentMapBoundary descendantCut parent child)
    (cut edge : Edge) :
    parentMapIncidence descendantCut parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  parentMapIncidence_eq_ite descendantCut parent child hboundary cut edge

theorem parentMapIncidence_self_closed
    {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex)
    (hboundary : ParentMapBoundary descendantCut parent child)
    (edge : Edge) :
    parentMapIncidence descendantCut parent child edge edge = 1 :=
  parentMapIncidence_self descendantCut parent child hboundary edge

theorem parentMapIncidence_ne_closed
    {Vertex Edge : Type*}
    (descendantCut : Edge → Vertex → Prop)
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    (parent child : Edge → Vertex)
    (hboundary : ParentMapBoundary descendantCut parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence descendantCut parent child cut edge = 0 :=
  parentMapIncidence_ne descendantCut parent child hboundary hne

theorem parentMapIncidenceCertificate_boundary_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child) :
    ParentMapBoundary descendantCut parent child :=
  parentMapIncidenceCertificate_boundary C

theorem parentMapIncidenceCertificate_eq_ite_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child)
    (cut edge : Edge) :
    parentMapIncidence descendantCut parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  parentMapIncidenceCertificate_eq_ite C cut edge

theorem parentMapIncidenceCertificate_self_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child)
    (edge : Edge) :
    parentMapIncidence descendantCut parent child edge edge = 1 :=
  parentMapIncidenceCertificate_self C edge

theorem parentMapIncidenceCertificate_ne_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {descendantCut : Edge → Vertex → Prop}
    [∀ cut vertex, Decidable (descendantCut cut vertex)]
    {parent child : Edge → Vertex}
    (C : ParentMapIncidenceCertificate descendantCut parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence descendantCut parent child cut edge = 0 :=
  parentMapIncidenceCertificate_ne C hne

theorem chainParentMapBoundary_closed {n : Nat} :
    ParentMapBoundary
      (@chainDescendantCut n) (@chainParent n) (@chainChild n) :=
  chainParentMapBoundary

theorem chainIncidence_eq_parentMapIncidence_closed
    {n : Nat} (cut edge : Fin n) :
    chainIncidence cut edge =
      @parentMapIncidence (Fin (n + 1)) (Fin n)
        (@chainDescendantCut n) (@chainDescendantCutDecidable n)
        (@chainParent n) (@chainChild n) cut edge :=
  chainIncidence_eq_parentMapIncidence cut edge

theorem chainIncidence_eq_ite_from_parentMapBoundary_closed
    {n : Nat} (cut edge : Fin n) :
    chainIncidence cut edge = if cut = edge then (1 : Int) else 0 :=
  chainIncidence_eq_ite_from_parentMapBoundary cut edge

theorem iteratedParentDescendantCut_child_closed
    {Vertex Edge : Type*} (parentStep : Vertex → Vertex)
    (child : Edge → Vertex) (edge : Edge) :
    iteratedParentDescendantCut parentStep child edge (child edge) :=
  iteratedParentDescendantCut_child parentStep child edge

theorem rank_iterate_parentStep_le_closed
    {Vertex : Type*} (parentStep : Vertex → Vertex)
    (rank : Vertex → Nat)
    (hstep : ∀ vertex : Vertex, rank (parentStep vertex) ≤ rank vertex)
    (n : Nat) (vertex : Vertex) :
    rank ((parentStep^[n]) vertex) ≤ rank vertex :=
  rank_iterate_parentStep_le parentStep rank hstep n vertex

theorem rankedRootedParentMap_parent_not_descendant_closed
    {Vertex Edge : Type*} {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (hdata : RankedRootedParentMapData parentStep parent child)
    (edge : Edge) :
    ¬ iteratedParentDescendantCut parentStep child edge (parent edge) :=
  rankedRootedParentMap_parent_not_descendant hdata edge

theorem rootedParentMapData_of_ranked_closed
    {Vertex Edge : Type*} {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (hdata : RankedRootedParentMapData parentStep parent child) :
    RootedParentMapData parentStep parent child :=
  rootedParentMapData_of_ranked hdata

theorem iteratedParentDescendantCut_child_of_parent_closed
    {Vertex Edge : Type*} {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge}
    (hparent :
      iteratedParentDescendantCut parentStep child cut (parent edge)) :
    iteratedParentDescendantCut parentStep child cut (child edge) :=
  iteratedParentDescendantCut_child_of_parent hdata hparent

theorem iteratedParentDescendantCut_parent_of_child_ne_closed
    {Vertex Edge : Type*} {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge)
    (hchild :
      iteratedParentDescendantCut parentStep child cut (child edge)) :
    iteratedParentDescendantCut parentStep child cut (parent edge) :=
  iteratedParentDescendantCut_parent_of_child_ne hdata hne hchild

theorem iteratedParentDescendantCut_child_iff_parent_of_ne_closed
    {Vertex Edge : Type*} {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    iteratedParentDescendantCut parentStep child cut (child edge) ↔
      iteratedParentDescendantCut parentStep child cut (parent edge) :=
  iteratedParentDescendantCut_child_iff_parent_of_ne hdata hne

theorem rootedParentMapBoundary_closed
    {Vertex Edge : Type*} {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (hdata : RootedParentMapData parentStep parent child) :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child :=
  rootedParentMapBoundary hdata

theorem rootedParentMapIncidence_eq_ite_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RootedParentMapData parentStep parent child)
    (cut edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  rootedParentMapIncidence_eq_ite hdata cut edge

theorem rootedParentMapIncidence_self_closed
    {Vertex Edge : Type*}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RootedParentMapData parentStep parent child)
    (edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child edge edge = 1 :=
  rootedParentMapIncidence_self hdata edge

theorem rootedParentMapIncidence_ne_closed
    {Vertex Edge : Type*}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge = 0 :=
  rootedParentMapIncidence_ne hdata hne

theorem rankedRootedParentMapBoundary_closed
    {Vertex Edge : Type*} {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    (hdata : RankedRootedParentMapData parentStep parent child) :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child :=
  rankedRootedParentMapBoundary hdata

theorem rankedRootedParentMapIncidence_eq_ite_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RankedRootedParentMapData parentStep parent child)
    (cut edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  rankedRootedParentMapIncidence_eq_ite hdata cut edge

theorem rankedRootedParentMapIncidence_self_closed
    {Vertex Edge : Type*}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RankedRootedParentMapData parentStep parent child)
    (edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child edge edge = 1 :=
  rankedRootedParentMapIncidence_self hdata edge

theorem rankedRootedParentMapIncidence_ne_closed
    {Vertex Edge : Type*}
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (hdata : RankedRootedParentMapData parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge = 0 :=
  rankedRootedParentMapIncidence_ne hdata hne

theorem rankedParentMapIncidenceCertificate_boundary_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child) :
    ParentMapBoundary
      (iteratedParentDescendantCut parentStep child) parent child :=
  rankedParentMapIncidenceCertificate_boundary C

theorem rankedParentMapIncidenceCertificate_eq_ite_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child)
    (cut edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge =
      if cut = edge then (1 : Int) else 0 :=
  rankedParentMapIncidenceCertificate_eq_ite C cut edge

theorem rankedParentMapIncidenceCertificate_self_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child)
    (edge : Edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child edge edge = 1 :=
  rankedParentMapIncidenceCertificate_self C edge

theorem rankedParentMapIncidenceCertificate_ne_closed
    {Vertex Edge : Type*} [DecidableEq Edge]
    {parentStep : Vertex → Vertex}
    {parent child : Edge → Vertex}
    [∀ cut vertex,
      Decidable (iteratedParentDescendantCut parentStep child cut vertex)]
    (C : RankedParentMapIncidenceCertificate parentStep parent child)
    {cut edge : Edge} (hne : cut ≠ edge) :
    parentMapIncidence
        (iteratedParentDescendantCut parentStep child)
        parent child cut edge = 0 :=
  rankedParentMapIncidenceCertificate_ne C hne

theorem d7Stage2CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage2CoforestDescendantCut
      d7Stage2CoforestParent
      d7Stage2CoforestChild :=
  d7Stage2CoforestParentMapBoundary

theorem d7Stage2CoforestEdgeTable_length_closed :
    d7Stage2CoforestEdgeTable.length = 4 :=
  d7Stage2CoforestEdgeTable_length

theorem d7Stage2CoforestVertexTable_length_closed :
    d7Stage2CoforestVertexTable.length = 5 :=
  d7Stage2CoforestVertexTable_length

theorem d7Stage2CoforestEdgeTable_nodup_closed :
    d7Stage2CoforestEdgeTable.Nodup :=
  d7Stage2CoforestEdgeTable_nodup

theorem d7Stage2CoforestVertexTable_nodup_closed :
    d7Stage2CoforestVertexTable.Nodup :=
  d7Stage2CoforestVertexTable_nodup

theorem d7Stage2CoforestParentTable_readout_closed :
    d7Stage2CoforestParentTable =
      [_root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v0,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12] :=
  d7Stage2CoforestParentTable_readout

theorem d7Stage2CoforestChildTable_readout_closed :
    d7Stage2CoforestChildTable =
      [_root_.EvenV11.TypeA.D7Stage2CoforestVertex.v0,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v3,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v4,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v5] :=
  d7Stage2CoforestChildTable_readout

theorem d7Stage2CoforestParentStepTable_readout_closed :
    d7Stage2CoforestParentStepTable =
      [_root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v0,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12] :=
  d7Stage2CoforestParentStepTable_readout

theorem d7Stage2CoforestRankTable_readout_closed :
    d7Stage2CoforestRankTable = [0, 1, 2, 1, 1] :=
  d7Stage2CoforestRankTable_readout

theorem d7Stage2Packet134Color34CoforestEdgeTable_length_closed :
    d7Stage2Packet134Color34CoforestEdgeTable.length = 4 :=
  d7Stage2Packet134Color34CoforestEdgeTable_length

theorem d7Stage2Packet134Color34CoforestVertexTable_length_closed :
    d7Stage2Packet134Color34CoforestVertexTable.length = 5 :=
  d7Stage2Packet134Color34CoforestVertexTable_length

theorem d7Stage2Packet134Color34CoforestEdgeTable_nodup_closed :
    d7Stage2Packet134Color34CoforestEdgeTable.Nodup :=
  d7Stage2Packet134Color34CoforestEdgeTable_nodup

theorem d7Stage2Packet134Color34CoforestVertexTable_nodup_closed :
    d7Stage2Packet134Color34CoforestVertexTable.Nodup :=
  d7Stage2Packet134Color34CoforestVertexTable_nodup

theorem d7Stage2Packet134Color34CoforestParentTable_readout_closed :
    d7Stage2Packet134Color34CoforestParentTable =
      [_root_.EvenV11.TypeA.TwoPathForkCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.left,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.right] :=
  d7Stage2Packet134Color34CoforestParentTable_readout

theorem d7Stage2Packet134Color34CoforestChildTable_readout_closed :
    d7Stage2Packet134Color34CoforestChildTable =
      [_root_.EvenV11.TypeA.TwoPathForkCoforestVertex.left,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.leftLeaf,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.right,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.rightLeaf] :=
  d7Stage2Packet134Color34CoforestChildTable_readout

theorem d7Stage2Packet134Color34CoforestParentStepTable_readout_closed :
    d7Stage2Packet134Color34CoforestParentStepTable =
      [_root_.EvenV11.TypeA.TwoPathForkCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.left,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoPathForkCoforestVertex.right] :=
  d7Stage2Packet134Color34CoforestParentStepTable_readout

theorem d7Stage2Packet134Color34CoforestRankTable_readout_closed :
    d7Stage2Packet134Color34CoforestRankTable = [0, 1, 2, 1, 2] :=
  d7Stage2Packet134Color34CoforestRankTable_readout

theorem d7Stage2Pair02Color0CoforestEdgeTable_length_closed :
    d7Stage2Pair02Color0CoforestEdgeTable.length = 4 :=
  d7Stage2Pair02Color0CoforestEdgeTable_length

theorem d7Stage2Pair02Color0CoforestVertexTable_length_closed :
    d7Stage2Pair02Color0CoforestVertexTable.length = 5 :=
  d7Stage2Pair02Color0CoforestVertexTable_length

theorem d7Stage2Pair02Color0CoforestEdgeTable_nodup_closed :
    d7Stage2Pair02Color0CoforestEdgeTable.Nodup :=
  d7Stage2Pair02Color0CoforestEdgeTable_nodup

theorem d7Stage2Pair02Color0CoforestVertexTable_nodup_closed :
    d7Stage2Pair02Color0CoforestVertexTable.Nodup :=
  d7Stage2Pair02Color0CoforestVertexTable_nodup

theorem d7Stage2Pair02Color0CoforestParentTable_readout_closed :
    d7Stage2Pair02Color0CoforestParentTable =
      [_root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root] :=
  d7Stage2Pair02Color0CoforestParentTable_readout

theorem d7Stage2Pair02Color0CoforestChildTable_readout_closed :
    d7Stage2Pair02Color0CoforestChildTable =
      [_root_.EvenV11.TypeA.FourLeafStarCoforestVertex.leaf1,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.leaf2,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.leaf3,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.leaf4] :=
  d7Stage2Pair02Color0CoforestChildTable_readout

theorem d7Stage2Pair02Color0CoforestParentStepTable_readout_closed :
    d7Stage2Pair02Color0CoforestParentStepTable =
      [_root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FourLeafStarCoforestVertex.root] :=
  d7Stage2Pair02Color0CoforestParentStepTable_readout

theorem d7Stage2Pair02Color0CoforestRankTable_readout_closed :
    d7Stage2Pair02Color0CoforestRankTable = [0, 1, 1, 1, 1] :=
  d7Stage2Pair02Color0CoforestRankTable_readout

theorem d7Stage2Pair02Color2CoforestEdgeTable_length_closed :
    d7Stage2Pair02Color2CoforestEdgeTable.length = 4 :=
  d7Stage2Pair02Color2CoforestEdgeTable_length

theorem d7Stage2Pair02Color2CoforestVertexTable_length_closed :
    d7Stage2Pair02Color2CoforestVertexTable.length = 5 :=
  d7Stage2Pair02Color2CoforestVertexTable_length

theorem d7Stage2Pair02Color2CoforestEdgeTable_nodup_closed :
    d7Stage2Pair02Color2CoforestEdgeTable.Nodup :=
  d7Stage2Pair02Color2CoforestEdgeTable_nodup

theorem d7Stage2Pair02Color2CoforestVertexTable_nodup_closed :
    d7Stage2Pair02Color2CoforestVertexTable.Nodup :=
  d7Stage2Pair02Color2CoforestVertexTable_nodup

theorem d7Stage2Pair02Color2CoforestParentTable_readout_closed :
    d7Stage2Pair02Color2CoforestParentTable =
      [_root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v0,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12] :=
  d7Stage2Pair02Color2CoforestParentTable_readout

theorem d7Stage2Pair02Color2CoforestChildTable_readout_closed :
    d7Stage2Pair02Color2CoforestChildTable =
      [_root_.EvenV11.TypeA.D7Stage2CoforestVertex.v0,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v3,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v4,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v5] :=
  d7Stage2Pair02Color2CoforestChildTable_readout

theorem d7Stage2Pair02Color2CoforestParentStepTable_readout_closed :
    d7Stage2Pair02Color2CoforestParentStepTable =
      [_root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.v0,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12,
        _root_.EvenV11.TypeA.D7Stage2CoforestVertex.root12] :=
  d7Stage2Pair02Color2CoforestParentStepTable_readout

theorem d7Stage2Pair02Color2CoforestRankTable_readout_closed :
    d7Stage2Pair02Color2CoforestRankTable = [0, 1, 2, 1, 1] :=
  d7Stage2Pair02Color2CoforestRankTable_readout

theorem d7Stage2Pair56Color56CoforestEdgeTable_length_closed :
    d7Stage2Pair56Color56CoforestEdgeTable.length = 4 :=
  d7Stage2Pair56Color56CoforestEdgeTable_length

theorem d7Stage2Pair56Color56CoforestVertexTable_length_closed :
    d7Stage2Pair56Color56CoforestVertexTable.length = 5 :=
  d7Stage2Pair56Color56CoforestVertexTable_length

theorem d7Stage2Pair56Color56CoforestEdgeTable_nodup_closed :
    d7Stage2Pair56Color56CoforestEdgeTable.Nodup :=
  d7Stage2Pair56Color56CoforestEdgeTable_nodup

theorem d7Stage2Pair56Color56CoforestVertexTable_nodup_closed :
    d7Stage2Pair56Color56CoforestVertexTable.Nodup :=
  d7Stage2Pair56Color56CoforestVertexTable_nodup

theorem d7Stage2Pair56Color56CoforestParentTable_readout_closed :
    d7Stage2Pair56Color56CoforestParentTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.hub] :=
  d7Stage2Pair56Color56CoforestParentTable_readout

theorem d7Stage2Pair56Color56CoforestChildTable_readout_closed :
    d7Stage2Pair56Color56CoforestChildTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.leaf1,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.leaf2,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.leaf3] :=
  d7Stage2Pair56Color56CoforestChildTable_readout

theorem d7Stage2Pair56Color56CoforestParentStepTable_readout_closed :
    d7Stage2Pair56Color56CoforestParentStepTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafNoMateCoforestVertex.hub] :=
  d7Stage2Pair56Color56CoforestParentStepTable_readout

theorem d7Stage2Pair56Color56CoforestRankTable_readout_closed :
    d7Stage2Pair56Color56CoforestRankTable = [0, 1, 2, 2, 2] :=
  d7Stage2Pair56Color56CoforestRankTable_readout

theorem d5Stage1CoforestEdgeTable_length_closed :
    d5Stage1CoforestEdgeTable.length = 3 :=
  d5Stage1CoforestEdgeTable_length

theorem d5Stage1CoforestVertexTable_length_closed :
    d5Stage1CoforestVertexTable.length = 4 :=
  d5Stage1CoforestVertexTable_length

theorem d5Stage1CoforestEdgeTable_nodup_closed :
    d5Stage1CoforestEdgeTable.Nodup :=
  d5Stage1CoforestEdgeTable_nodup

theorem d5Stage1CoforestVertexTable_nodup_closed :
    d5Stage1CoforestVertexTable.Nodup :=
  d5Stage1CoforestVertexTable_nodup

theorem d5Stage1CoforestParentTable_readout_closed :
    d5Stage1CoforestParentTable =
      [_root_.EvenV11.TypeA.D5Stage1CoforestVertex.root0,
        _root_.EvenV11.TypeA.D5Stage1CoforestVertex.root0,
        _root_.EvenV11.TypeA.D5Stage1CoforestVertex.root0] :=
  d5Stage1CoforestParentTable_readout

theorem d5Stage1CoforestChildTable_readout_closed :
    d5Stage1CoforestChildTable =
      [_root_.EvenV11.TypeA.D5Stage1CoforestVertex.v1,
        _root_.EvenV11.TypeA.D5Stage1CoforestVertex.v2,
        _root_.EvenV11.TypeA.D5Stage1CoforestVertex.v3] :=
  d5Stage1CoforestChildTable_readout

theorem d5Stage1CoforestParentStepTable_readout_closed :
    d5Stage1CoforestParentStepTable =
      [_root_.EvenV11.TypeA.D5Stage1CoforestVertex.root0,
        _root_.EvenV11.TypeA.D5Stage1CoforestVertex.root0,
        _root_.EvenV11.TypeA.D5Stage1CoforestVertex.root0,
        _root_.EvenV11.TypeA.D5Stage1CoforestVertex.root0] :=
  d5Stage1CoforestParentStepTable_readout

theorem d5Stage1CoforestRankTable_readout_closed :
    d5Stage1CoforestRankTable = [0, 1, 1, 1] :=
  d5Stage1CoforestRankTable_readout

theorem d5Stage1PairCoforestEdgeTable_length_closed :
    d5Stage1PairCoforestEdgeTable.length = 3 :=
  d5Stage1PairCoforestEdgeTable_length

theorem d5Stage1PairCoforestVertexTable_length_closed :
    d5Stage1PairCoforestVertexTable.length = 4 :=
  d5Stage1PairCoforestVertexTable_length

theorem d5Stage1PairCoforestEdgeTable_nodup_closed :
    d5Stage1PairCoforestEdgeTable.Nodup :=
  d5Stage1PairCoforestEdgeTable_nodup

theorem d5Stage1PairCoforestVertexTable_nodup_closed :
    d5Stage1PairCoforestVertexTable.Nodup :=
  d5Stage1PairCoforestVertexTable_nodup

theorem d5Stage1PairCoforestParentTable_readout_closed :
    d5Stage1PairCoforestParentTable =
      [_root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.root3,
        _root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.v0,
        _root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.root3] :=
  d5Stage1PairCoforestParentTable_readout

theorem d5Stage1PairCoforestChildTable_readout_closed :
    d5Stage1PairCoforestChildTable =
      [_root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.v0,
        _root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.v1,
        _root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.v4] :=
  d5Stage1PairCoforestChildTable_readout

theorem d5Stage1PairCoforestParentStepTable_readout_closed :
    d5Stage1PairCoforestParentStepTable =
      [_root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.root3,
        _root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.root3,
        _root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.v0,
        _root_.EvenV11.TypeA.D5Stage1PairCoforestVertex.root3] :=
  d5Stage1PairCoforestParentStepTable_readout

theorem d5Stage1PairCoforestRankTable_readout_closed :
    d5Stage1PairCoforestRankTable = [0, 1, 2, 1] :=
  d5Stage1PairCoforestRankTable_readout

theorem d5Stage2TripleColor0CoforestEdgeTable_length_closed :
    d5Stage2TripleColor0CoforestEdgeTable.length = 2 :=
  d5Stage2TripleColor0CoforestEdgeTable_length

theorem d5Stage2TripleColor0CoforestVertexTable_length_closed :
    d5Stage2TripleColor0CoforestVertexTable.length = 3 :=
  d5Stage2TripleColor0CoforestVertexTable_length

theorem d5Stage2TripleColor0CoforestEdgeTable_nodup_closed :
    d5Stage2TripleColor0CoforestEdgeTable.Nodup :=
  d5Stage2TripleColor0CoforestEdgeTable_nodup

theorem d5Stage2TripleColor0CoforestVertexTable_nodup_closed :
    d5Stage2TripleColor0CoforestVertexTable.Nodup :=
  d5Stage2TripleColor0CoforestVertexTable_nodup

theorem d5Stage2TripleColor0CoforestParentTable_readout_closed :
    d5Stage2TripleColor0CoforestParentTable =
      [_root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root] :=
  d5Stage2TripleColor0CoforestParentTable_readout

theorem d5Stage2TripleColor0CoforestChildTable_readout_closed :
    d5Stage2TripleColor0CoforestChildTable =
      [_root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.left,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.right] :=
  d5Stage2TripleColor0CoforestChildTable_readout

theorem d5Stage2TripleColor0CoforestParentStepTable_readout_closed :
    d5Stage2TripleColor0CoforestParentStepTable =
      [_root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root] :=
  d5Stage2TripleColor0CoforestParentStepTable_readout

theorem d5Stage2TripleColor0CoforestRankTable_readout_closed :
    d5Stage2TripleColor0CoforestRankTable = [0, 1, 1] :=
  d5Stage2TripleColor0CoforestRankTable_readout

theorem d5Stage2TripleColor43CoforestEdgeTable_length_closed :
    d5Stage2TripleColor43CoforestEdgeTable.length = 2 :=
  d5Stage2TripleColor43CoforestEdgeTable_length

theorem d5Stage2TripleColor43CoforestVertexTable_length_closed :
    d5Stage2TripleColor43CoforestVertexTable.length = 3 :=
  d5Stage2TripleColor43CoforestVertexTable_length

theorem d5Stage2TripleColor43CoforestEdgeTable_nodup_closed :
    d5Stage2TripleColor43CoforestEdgeTable.Nodup :=
  d5Stage2TripleColor43CoforestEdgeTable_nodup

theorem d5Stage2TripleColor43CoforestVertexTable_nodup_closed :
    d5Stage2TripleColor43CoforestVertexTable.Nodup :=
  d5Stage2TripleColor43CoforestVertexTable_nodup

theorem d5Stage2TripleColor43CoforestParentTable_readout_closed :
    d5Stage2TripleColor43CoforestParentTable =
      [_root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.middle] :=
  d5Stage2TripleColor43CoforestParentTable_readout

theorem d5Stage2TripleColor43CoforestChildTable_readout_closed :
    d5Stage2TripleColor43CoforestChildTable =
      [_root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.middle,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.leaf] :=
  d5Stage2TripleColor43CoforestChildTable_readout

theorem d5Stage2TripleColor43CoforestParentStepTable_readout_closed :
    d5Stage2TripleColor43CoforestParentStepTable =
      [_root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.middle] :=
  d5Stage2TripleColor43CoforestParentStepTable_readout

theorem d5Stage2TripleColor43CoforestRankTable_readout_closed :
    d5Stage2TripleColor43CoforestRankTable = [0, 1, 2] :=
  d5Stage2TripleColor43CoforestRankTable_readout

theorem d5Stage2PairColor1CoforestEdgeTable_length_closed :
    d5Stage2PairColor1CoforestEdgeTable.length = 2 :=
  d5Stage2PairColor1CoforestEdgeTable_length

theorem d5Stage2PairColor1CoforestVertexTable_length_closed :
    d5Stage2PairColor1CoforestVertexTable.length = 3 :=
  d5Stage2PairColor1CoforestVertexTable_length

theorem d5Stage2PairColor1CoforestEdgeTable_nodup_closed :
    d5Stage2PairColor1CoforestEdgeTable.Nodup :=
  d5Stage2PairColor1CoforestEdgeTable_nodup

theorem d5Stage2PairColor1CoforestVertexTable_nodup_closed :
    d5Stage2PairColor1CoforestVertexTable.Nodup :=
  d5Stage2PairColor1CoforestVertexTable_nodup

theorem d5Stage2PairColor1CoforestParentTable_readout_closed :
    d5Stage2PairColor1CoforestParentTable =
      [_root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.middle] :=
  d5Stage2PairColor1CoforestParentTable_readout

theorem d5Stage2PairColor1CoforestChildTable_readout_closed :
    d5Stage2PairColor1CoforestChildTable =
      [_root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.middle,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.leaf] :=
  d5Stage2PairColor1CoforestChildTable_readout

theorem d5Stage2PairColor1CoforestParentStepTable_readout_closed :
    d5Stage2PairColor1CoforestParentStepTable =
      [_root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoEdgePathCoforestVertex.middle] :=
  d5Stage2PairColor1CoforestParentStepTable_readout

theorem d5Stage2PairColor1CoforestRankTable_readout_closed :
    d5Stage2PairColor1CoforestRankTable = [0, 1, 2] :=
  d5Stage2PairColor1CoforestRankTable_readout

theorem d5Stage2PairColor2CoforestEdgeTable_length_closed :
    d5Stage2PairColor2CoforestEdgeTable.length = 2 :=
  d5Stage2PairColor2CoforestEdgeTable_length

theorem d5Stage2PairColor2CoforestVertexTable_length_closed :
    d5Stage2PairColor2CoforestVertexTable.length = 3 :=
  d5Stage2PairColor2CoforestVertexTable_length

theorem d5Stage2PairColor2CoforestEdgeTable_nodup_closed :
    d5Stage2PairColor2CoforestEdgeTable.Nodup :=
  d5Stage2PairColor2CoforestEdgeTable_nodup

theorem d5Stage2PairColor2CoforestVertexTable_nodup_closed :
    d5Stage2PairColor2CoforestVertexTable.Nodup :=
  d5Stage2PairColor2CoforestVertexTable_nodup

theorem d5Stage2PairColor2CoforestParentTable_readout_closed :
    d5Stage2PairColor2CoforestParentTable =
      [_root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root] :=
  d5Stage2PairColor2CoforestParentTable_readout

theorem d5Stage2PairColor2CoforestChildTable_readout_closed :
    d5Stage2PairColor2CoforestChildTable =
      [_root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.left,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.right] :=
  d5Stage2PairColor2CoforestChildTable_readout

theorem d5Stage2PairColor2CoforestParentStepTable_readout_closed :
    d5Stage2PairColor2CoforestParentStepTable =
      [_root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.TwoLeafStarCoforestVertex.root] :=
  d5Stage2PairColor2CoforestParentStepTable_readout

theorem d5Stage2PairColor2CoforestRankTable_readout_closed :
    d5Stage2PairColor2CoforestRankTable = [0, 1, 1] :=
  d5Stage2PairColor2CoforestRankTable_readout

theorem d5Stage3FinalPairColor0CoforestEdgeTable_length_closed :
    d5Stage3FinalPairColor0CoforestEdgeTable.length = 1 :=
  d5Stage3FinalPairColor0CoforestEdgeTable_length

theorem d5Stage3FinalPairColor0CoforestVertexTable_length_closed :
    d5Stage3FinalPairColor0CoforestVertexTable.length = 2 :=
  d5Stage3FinalPairColor0CoforestVertexTable_length

theorem d5Stage3FinalPairColor0CoforestEdgeTable_nodup_closed :
    d5Stage3FinalPairColor0CoforestEdgeTable.Nodup :=
  d5Stage3FinalPairColor0CoforestEdgeTable_nodup

theorem d5Stage3FinalPairColor0CoforestVertexTable_nodup_closed :
    d5Stage3FinalPairColor0CoforestVertexTable.Nodup :=
  d5Stage3FinalPairColor0CoforestVertexTable_nodup

theorem d5Stage3FinalPairColor0CoforestParentTable_readout_closed :
    d5Stage3FinalPairColor0CoforestParentTable =
      [_root_.EvenV11.TypeA.OneEdgeCoforestVertex.root] :=
  d5Stage3FinalPairColor0CoforestParentTable_readout

theorem d5Stage3FinalPairColor0CoforestChildTable_readout_closed :
    d5Stage3FinalPairColor0CoforestChildTable =
      [_root_.EvenV11.TypeA.OneEdgeCoforestVertex.leaf] :=
  d5Stage3FinalPairColor0CoforestChildTable_readout

theorem d5Stage3FinalPairColor0CoforestParentStepTable_readout_closed :
    d5Stage3FinalPairColor0CoforestParentStepTable =
      [_root_.EvenV11.TypeA.OneEdgeCoforestVertex.root,
        _root_.EvenV11.TypeA.OneEdgeCoforestVertex.root] :=
  d5Stage3FinalPairColor0CoforestParentStepTable_readout

theorem d5Stage3FinalPairColor0CoforestRankTable_readout_closed :
    d5Stage3FinalPairColor0CoforestRankTable = [0, 1] :=
  d5Stage3FinalPairColor0CoforestRankTable_readout

theorem d5Stage3FinalPairColor2CoforestEdgeTable_length_closed :
    d5Stage3FinalPairColor2CoforestEdgeTable.length = 1 :=
  d5Stage3FinalPairColor2CoforestEdgeTable_length

theorem d5Stage3FinalPairColor2CoforestVertexTable_length_closed :
    d5Stage3FinalPairColor2CoforestVertexTable.length = 2 :=
  d5Stage3FinalPairColor2CoforestVertexTable_length

theorem d5Stage3FinalPairColor2CoforestEdgeTable_nodup_closed :
    d5Stage3FinalPairColor2CoforestEdgeTable.Nodup :=
  d5Stage3FinalPairColor2CoforestEdgeTable_nodup

theorem d5Stage3FinalPairColor2CoforestVertexTable_nodup_closed :
    d5Stage3FinalPairColor2CoforestVertexTable.Nodup :=
  d5Stage3FinalPairColor2CoforestVertexTable_nodup

theorem d5Stage3FinalPairColor2CoforestParentTable_readout_closed :
    d5Stage3FinalPairColor2CoforestParentTable =
      [_root_.EvenV11.TypeA.OneEdgeCoforestVertex.root] :=
  d5Stage3FinalPairColor2CoforestParentTable_readout

theorem d5Stage3FinalPairColor2CoforestChildTable_readout_closed :
    d5Stage3FinalPairColor2CoforestChildTable =
      [_root_.EvenV11.TypeA.OneEdgeCoforestVertex.leaf] :=
  d5Stage3FinalPairColor2CoforestChildTable_readout

theorem d5Stage3FinalPairColor2CoforestParentStepTable_readout_closed :
    d5Stage3FinalPairColor2CoforestParentStepTable =
      [_root_.EvenV11.TypeA.OneEdgeCoforestVertex.root,
        _root_.EvenV11.TypeA.OneEdgeCoforestVertex.root] :=
  d5Stage3FinalPairColor2CoforestParentStepTable_readout

theorem d5Stage3FinalPairColor2CoforestRankTable_readout_closed :
    d5Stage3FinalPairColor2CoforestRankTable = [0, 1] :=
  d5Stage3FinalPairColor2CoforestRankTable_readout

theorem d5Stage1CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage1CoforestDescendantCut
      d5Stage1CoforestParent
      d5Stage1CoforestChild :=
  d5Stage1CoforestParentMapBoundary

theorem d5Stage1CoforestIncidence_eq_ite_closed
    (cut edge : D5Stage1CoforestEdge) :
    @parentMapIncidence
        D5Stage1CoforestVertex D5Stage1CoforestEdge
        d5Stage1CoforestDescendantCut
        d5Stage1CoforestDescendantCutDecidable
        d5Stage1CoforestParent d5Stage1CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage1CoforestIncidence_eq_ite cut edge

theorem d5Stage1CoforestIncidence_self_closed
    (edge : D5Stage1CoforestEdge) :
    @parentMapIncidence
        D5Stage1CoforestVertex D5Stage1CoforestEdge
        d5Stage1CoforestDescendantCut
        d5Stage1CoforestDescendantCutDecidable
        d5Stage1CoforestParent d5Stage1CoforestChild edge edge = 1 :=
  d5Stage1CoforestIncidence_self edge

theorem d5Stage1CoforestIncidence_ne_closed
    {cut edge : D5Stage1CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage1CoforestVertex D5Stage1CoforestEdge
        d5Stage1CoforestDescendantCut
        d5Stage1CoforestDescendantCutDecidable
        d5Stage1CoforestParent d5Stage1CoforestChild cut edge = 0 :=
  d5Stage1CoforestIncidence_ne hne

theorem d5Stage1CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut d5Stage1CoforestParentStep
        d5Stage1CoforestChild)
      d5Stage1CoforestParent
      d5Stage1CoforestChild :=
  d5Stage1CoforestIteratedParentMapBoundary

theorem d5Stage1PairCoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage1PairCoforestDescendantCut
      d5Stage1PairCoforestParent
      d5Stage1PairCoforestChild :=
  d5Stage1PairCoforestParentMapBoundary

theorem d5Stage1PairCoforestIncidence_eq_ite_closed
    (cut edge : D5Stage1PairCoforestEdge) :
    @parentMapIncidence
        D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
        d5Stage1PairCoforestDescendantCut
        d5Stage1PairCoforestDescendantCutDecidable
        d5Stage1PairCoforestParent
        d5Stage1PairCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage1PairCoforestIncidence_eq_ite cut edge

theorem d5Stage1PairCoforestIncidence_self_closed
    (edge : D5Stage1PairCoforestEdge) :
    @parentMapIncidence
        D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
        d5Stage1PairCoforestDescendantCut
        d5Stage1PairCoforestDescendantCutDecidable
        d5Stage1PairCoforestParent
        d5Stage1PairCoforestChild edge edge = 1 :=
  d5Stage1PairCoforestIncidence_self edge

theorem d5Stage1PairCoforestIncidence_ne_closed
    {cut edge : D5Stage1PairCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage1PairCoforestVertex D5Stage1PairCoforestEdge
        d5Stage1PairCoforestDescendantCut
        d5Stage1PairCoforestDescendantCutDecidable
        d5Stage1PairCoforestParent
        d5Stage1PairCoforestChild cut edge = 0 :=
  d5Stage1PairCoforestIncidence_ne hne

theorem d5Stage1PairCoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut d5Stage1PairCoforestParentStep
        d5Stage1PairCoforestChild)
      d5Stage1PairCoforestParent
      d5Stage1PairCoforestChild :=
  d5Stage1PairCoforestIteratedParentMapBoundary

theorem d5Stage2TripleColor0CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage2TripleColor0CoforestDescendantCut
      d5Stage2TripleColor0CoforestParent
      d5Stage2TripleColor0CoforestChild :=
  d5Stage2TripleColor0CoforestParentMapBoundary

theorem d5Stage2TripleColor0CoforestIncidence_eq_ite_closed
    (cut edge : D5Stage2TripleColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor0CoforestVertex
        D5Stage2TripleColor0CoforestEdge
        d5Stage2TripleColor0CoforestDescendantCut
        d5Stage2TripleColor0CoforestDescendantCutDecidable
        d5Stage2TripleColor0CoforestParent
        d5Stage2TripleColor0CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage2TripleColor0CoforestIncidence_eq_ite cut edge

theorem d5Stage2TripleColor0CoforestIncidence_self_closed
    (edge : D5Stage2TripleColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor0CoforestVertex
        D5Stage2TripleColor0CoforestEdge
        d5Stage2TripleColor0CoforestDescendantCut
        d5Stage2TripleColor0CoforestDescendantCutDecidable
        d5Stage2TripleColor0CoforestParent
        d5Stage2TripleColor0CoforestChild edge edge = 1 :=
  d5Stage2TripleColor0CoforestIncidence_self edge

theorem d5Stage2TripleColor0CoforestIncidence_ne_closed
    {cut edge : D5Stage2TripleColor0CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2TripleColor0CoforestVertex
        D5Stage2TripleColor0CoforestEdge
        d5Stage2TripleColor0CoforestDescendantCut
        d5Stage2TripleColor0CoforestDescendantCutDecidable
        d5Stage2TripleColor0CoforestParent
        d5Stage2TripleColor0CoforestChild cut edge = 0 :=
  d5Stage2TripleColor0CoforestIncidence_ne hne

theorem d5Stage2TripleColor0CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2TripleColor0CoforestParentStep
        d5Stage2TripleColor0CoforestChild)
      d5Stage2TripleColor0CoforestParent
      d5Stage2TripleColor0CoforestChild :=
  d5Stage2TripleColor0CoforestIteratedParentMapBoundary

theorem d5Stage2TripleColor43CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage2TripleColor43CoforestDescendantCut
      d5Stage2TripleColor43CoforestParent
      d5Stage2TripleColor43CoforestChild :=
  d5Stage2TripleColor43CoforestParentMapBoundary

theorem d5Stage2TripleColor43CoforestIncidence_eq_ite_closed
    (cut edge : D5Stage2TripleColor43CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor43CoforestVertex
        D5Stage2TripleColor43CoforestEdge
        d5Stage2TripleColor43CoforestDescendantCut
        d5Stage2TripleColor43CoforestDescendantCutDecidable
        d5Stage2TripleColor43CoforestParent
        d5Stage2TripleColor43CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage2TripleColor43CoforestIncidence_eq_ite cut edge

theorem d5Stage2TripleColor43CoforestIncidence_self_closed
    (edge : D5Stage2TripleColor43CoforestEdge) :
    @parentMapIncidence
        D5Stage2TripleColor43CoforestVertex
        D5Stage2TripleColor43CoforestEdge
        d5Stage2TripleColor43CoforestDescendantCut
        d5Stage2TripleColor43CoforestDescendantCutDecidable
        d5Stage2TripleColor43CoforestParent
        d5Stage2TripleColor43CoforestChild edge edge = 1 :=
  d5Stage2TripleColor43CoforestIncidence_self edge

theorem d5Stage2TripleColor43CoforestIncidence_ne_closed
    {cut edge : D5Stage2TripleColor43CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2TripleColor43CoforestVertex
        D5Stage2TripleColor43CoforestEdge
        d5Stage2TripleColor43CoforestDescendantCut
        d5Stage2TripleColor43CoforestDescendantCutDecidable
        d5Stage2TripleColor43CoforestParent
        d5Stage2TripleColor43CoforestChild cut edge = 0 :=
  d5Stage2TripleColor43CoforestIncidence_ne hne

theorem d5Stage2TripleColor43CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2TripleColor43CoforestParentStep
        d5Stage2TripleColor43CoforestChild)
      d5Stage2TripleColor43CoforestParent
      d5Stage2TripleColor43CoforestChild :=
  d5Stage2TripleColor43CoforestIteratedParentMapBoundary

theorem d5Stage2PairColor1CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage2PairColor1CoforestDescendantCut
      d5Stage2PairColor1CoforestParent
      d5Stage2PairColor1CoforestChild :=
  d5Stage2PairColor1CoforestParentMapBoundary

theorem d5Stage2PairColor1CoforestIncidence_eq_ite_closed
    (cut edge : D5Stage2PairColor1CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor1CoforestVertex
        D5Stage2PairColor1CoforestEdge
        d5Stage2PairColor1CoforestDescendantCut
        d5Stage2PairColor1CoforestDescendantCutDecidable
        d5Stage2PairColor1CoforestParent
        d5Stage2PairColor1CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage2PairColor1CoforestIncidence_eq_ite cut edge

theorem d5Stage2PairColor1CoforestIncidence_self_closed
    (edge : D5Stage2PairColor1CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor1CoforestVertex
        D5Stage2PairColor1CoforestEdge
        d5Stage2PairColor1CoforestDescendantCut
        d5Stage2PairColor1CoforestDescendantCutDecidable
        d5Stage2PairColor1CoforestParent
        d5Stage2PairColor1CoforestChild edge edge = 1 :=
  d5Stage2PairColor1CoforestIncidence_self edge

theorem d5Stage2PairColor1CoforestIncidence_ne_closed
    {cut edge : D5Stage2PairColor1CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2PairColor1CoforestVertex
        D5Stage2PairColor1CoforestEdge
        d5Stage2PairColor1CoforestDescendantCut
        d5Stage2PairColor1CoforestDescendantCutDecidable
        d5Stage2PairColor1CoforestParent
        d5Stage2PairColor1CoforestChild cut edge = 0 :=
  d5Stage2PairColor1CoforestIncidence_ne hne

theorem d5Stage2PairColor1CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2PairColor1CoforestParentStep
        d5Stage2PairColor1CoforestChild)
      d5Stage2PairColor1CoforestParent
      d5Stage2PairColor1CoforestChild :=
  d5Stage2PairColor1CoforestIteratedParentMapBoundary

theorem d5Stage2PairColor2CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage2PairColor2CoforestDescendantCut
      d5Stage2PairColor2CoforestParent
      d5Stage2PairColor2CoforestChild :=
  d5Stage2PairColor2CoforestParentMapBoundary

theorem d5Stage2PairColor2CoforestIncidence_eq_ite_closed
    (cut edge : D5Stage2PairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor2CoforestVertex
        D5Stage2PairColor2CoforestEdge
        d5Stage2PairColor2CoforestDescendantCut
        d5Stage2PairColor2CoforestDescendantCutDecidable
        d5Stage2PairColor2CoforestParent
        d5Stage2PairColor2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage2PairColor2CoforestIncidence_eq_ite cut edge

theorem d5Stage2PairColor2CoforestIncidence_self_closed
    (edge : D5Stage2PairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage2PairColor2CoforestVertex
        D5Stage2PairColor2CoforestEdge
        d5Stage2PairColor2CoforestDescendantCut
        d5Stage2PairColor2CoforestDescendantCutDecidable
        d5Stage2PairColor2CoforestParent
        d5Stage2PairColor2CoforestChild edge edge = 1 :=
  d5Stage2PairColor2CoforestIncidence_self edge

theorem d5Stage2PairColor2CoforestIncidence_ne_closed
    {cut edge : D5Stage2PairColor2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage2PairColor2CoforestVertex
        D5Stage2PairColor2CoforestEdge
        d5Stage2PairColor2CoforestDescendantCut
        d5Stage2PairColor2CoforestDescendantCutDecidable
        d5Stage2PairColor2CoforestParent
        d5Stage2PairColor2CoforestChild cut edge = 0 :=
  d5Stage2PairColor2CoforestIncidence_ne hne

theorem d5Stage2PairColor2CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage2PairColor2CoforestParentStep
        d5Stage2PairColor2CoforestChild)
      d5Stage2PairColor2CoforestParent
      d5Stage2PairColor2CoforestChild :=
  d5Stage2PairColor2CoforestIteratedParentMapBoundary

theorem d5Stage3FinalPairColor0CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage3FinalPairColor0CoforestDescendantCut
      d5Stage3FinalPairColor0CoforestParent
      d5Stage3FinalPairColor0CoforestChild :=
  d5Stage3FinalPairColor0CoforestParentMapBoundary

theorem d5Stage3FinalPairColor0CoforestIncidence_eq_ite_closed
    (cut edge : D5Stage3FinalPairColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor0CoforestVertex
        D5Stage3FinalPairColor0CoforestEdge
        d5Stage3FinalPairColor0CoforestDescendantCut
        d5Stage3FinalPairColor0CoforestDescendantCutDecidable
        d5Stage3FinalPairColor0CoforestParent
        d5Stage3FinalPairColor0CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage3FinalPairColor0CoforestIncidence_eq_ite cut edge

theorem d5Stage3FinalPairColor0CoforestIncidence_self_closed
    (edge : D5Stage3FinalPairColor0CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor0CoforestVertex
        D5Stage3FinalPairColor0CoforestEdge
        d5Stage3FinalPairColor0CoforestDescendantCut
        d5Stage3FinalPairColor0CoforestDescendantCutDecidable
        d5Stage3FinalPairColor0CoforestParent
        d5Stage3FinalPairColor0CoforestChild edge edge = 1 :=
  d5Stage3FinalPairColor0CoforestIncidence_self edge

theorem d5Stage3FinalPairColor0CoforestIncidence_ne_closed
    {cut edge : D5Stage3FinalPairColor0CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage3FinalPairColor0CoforestVertex
        D5Stage3FinalPairColor0CoforestEdge
        d5Stage3FinalPairColor0CoforestDescendantCut
        d5Stage3FinalPairColor0CoforestDescendantCutDecidable
        d5Stage3FinalPairColor0CoforestParent
        d5Stage3FinalPairColor0CoforestChild cut edge = 0 :=
  d5Stage3FinalPairColor0CoforestIncidence_ne hne

theorem d5Stage3FinalPairColor0CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage3FinalPairColor0CoforestParentStep
        d5Stage3FinalPairColor0CoforestChild)
      d5Stage3FinalPairColor0CoforestParent
      d5Stage3FinalPairColor0CoforestChild :=
  d5Stage3FinalPairColor0CoforestIteratedParentMapBoundary

theorem d5Stage3FinalPairColor2CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d5Stage3FinalPairColor2CoforestDescendantCut
      d5Stage3FinalPairColor2CoforestParent
      d5Stage3FinalPairColor2CoforestChild :=
  d5Stage3FinalPairColor2CoforestParentMapBoundary

theorem d5Stage3FinalPairColor2CoforestIncidence_eq_ite_closed
    (cut edge : D5Stage3FinalPairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor2CoforestVertex
        D5Stage3FinalPairColor2CoforestEdge
        d5Stage3FinalPairColor2CoforestDescendantCut
        d5Stage3FinalPairColor2CoforestDescendantCutDecidable
        d5Stage3FinalPairColor2CoforestParent
        d5Stage3FinalPairColor2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d5Stage3FinalPairColor2CoforestIncidence_eq_ite cut edge

theorem d5Stage3FinalPairColor2CoforestIncidence_self_closed
    (edge : D5Stage3FinalPairColor2CoforestEdge) :
    @parentMapIncidence
        D5Stage3FinalPairColor2CoforestVertex
        D5Stage3FinalPairColor2CoforestEdge
        d5Stage3FinalPairColor2CoforestDescendantCut
        d5Stage3FinalPairColor2CoforestDescendantCutDecidable
        d5Stage3FinalPairColor2CoforestParent
        d5Stage3FinalPairColor2CoforestChild edge edge = 1 :=
  d5Stage3FinalPairColor2CoforestIncidence_self edge

theorem d5Stage3FinalPairColor2CoforestIncidence_ne_closed
    {cut edge : D5Stage3FinalPairColor2CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D5Stage3FinalPairColor2CoforestVertex
        D5Stage3FinalPairColor2CoforestEdge
        d5Stage3FinalPairColor2CoforestDescendantCut
        d5Stage3FinalPairColor2CoforestDescendantCutDecidable
        d5Stage3FinalPairColor2CoforestParent
        d5Stage3FinalPairColor2CoforestChild cut edge = 0 :=
  d5Stage3FinalPairColor2CoforestIncidence_ne hne

theorem d5Stage3FinalPairColor2CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d5Stage3FinalPairColor2CoforestParentStep
        d5Stage3FinalPairColor2CoforestChild)
      d5Stage3FinalPairColor2CoforestParent
      d5Stage3FinalPairColor2CoforestChild :=
  d5Stage3FinalPairColor2CoforestIteratedParentMapBoundary

theorem d7Stage1TripleCoforestEdgeTable_length_closed :
    d7Stage1TripleCoforestEdgeTable.length = 5 :=
  d7Stage1TripleCoforestEdgeTable_length

theorem d7Stage1TripleCoforestVertexTable_length_closed :
    d7Stage1TripleCoforestVertexTable.length = 6 :=
  d7Stage1TripleCoforestVertexTable_length

theorem d7Stage1TripleCoforestEdgeTable_nodup_closed :
    d7Stage1TripleCoforestEdgeTable.Nodup :=
  d7Stage1TripleCoforestEdgeTable_nodup

theorem d7Stage1TripleCoforestVertexTable_nodup_closed :
    d7Stage1TripleCoforestVertexTable.Nodup :=
  d7Stage1TripleCoforestVertexTable_nodup

theorem d7Stage1TripleCoforestParentTable_readout_closed :
    d7Stage1TripleCoforestParentTable =
      [_root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root] :=
  d7Stage1TripleCoforestParentTable_readout

theorem d7Stage1TripleCoforestChildTable_readout_closed :
    d7Stage1TripleCoforestChildTable =
      [_root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.leaf1,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.leaf2,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.leaf3,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.leaf4,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.leaf5] :=
  d7Stage1TripleCoforestChildTable_readout

theorem d7Stage1TripleCoforestParentStepTable_readout_closed :
    d7Stage1TripleCoforestParentStepTable =
      [_root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root,
        _root_.EvenV11.TypeA.FiveLeafStarCoforestVertex.root] :=
  d7Stage1TripleCoforestParentStepTable_readout

theorem d7Stage1TripleCoforestRankTable_readout_closed :
    d7Stage1TripleCoforestRankTable = [0, 1, 1, 1, 1, 1] :=
  d7Stage1TripleCoforestRankTable_readout

theorem d7Stage1Pair34CoforestEdgeTable_length_closed :
    d7Stage1Pair34CoforestEdgeTable.length = 5 :=
  d7Stage1Pair34CoforestEdgeTable_length

theorem d7Stage1Pair34CoforestVertexTable_length_closed :
    d7Stage1Pair34CoforestVertexTable.length = 6 :=
  d7Stage1Pair34CoforestVertexTable_length

theorem d7Stage1Pair34CoforestEdgeTable_nodup_closed :
    d7Stage1Pair34CoforestEdgeTable.Nodup :=
  d7Stage1Pair34CoforestEdgeTable_nodup

theorem d7Stage1Pair34CoforestVertexTable_nodup_closed :
    d7Stage1Pair34CoforestVertexTable.Nodup :=
  d7Stage1Pair34CoforestVertexTable_nodup

theorem d7Stage1Pair34CoforestParentTable_readout_closed :
    d7Stage1Pair34CoforestParentTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root] :=
  d7Stage1Pair34CoforestParentTable_readout

theorem d7Stage1Pair34CoforestChildTable_readout_closed :
    d7Stage1Pair34CoforestChildTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.leaf1,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.leaf2,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.leaf3,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.mate] :=
  d7Stage1Pair34CoforestChildTable_readout

theorem d7Stage1Pair34CoforestParentStepTable_readout_closed :
    d7Stage1Pair34CoforestParentStepTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root] :=
  d7Stage1Pair34CoforestParentStepTable_readout

theorem d7Stage1Pair34CoforestRankTable_readout_closed :
    d7Stage1Pair34CoforestRankTable = [0, 1, 2, 2, 2, 1] :=
  d7Stage1Pair34CoforestRankTable_readout

theorem d7Stage1Pair56CoforestEdgeTable_length_closed :
    d7Stage1Pair56CoforestEdgeTable.length = 5 :=
  d7Stage1Pair56CoforestEdgeTable_length

theorem d7Stage1Pair56CoforestVertexTable_length_closed :
    d7Stage1Pair56CoforestVertexTable.length = 6 :=
  d7Stage1Pair56CoforestVertexTable_length

theorem d7Stage1Pair56CoforestEdgeTable_nodup_closed :
    d7Stage1Pair56CoforestEdgeTable.Nodup :=
  d7Stage1Pair56CoforestEdgeTable_nodup

theorem d7Stage1Pair56CoforestVertexTable_nodup_closed :
    d7Stage1Pair56CoforestVertexTable.Nodup :=
  d7Stage1Pair56CoforestVertexTable_nodup

theorem d7Stage1Pair56CoforestParentTable_readout_closed :
    d7Stage1Pair56CoforestParentTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root] :=
  d7Stage1Pair56CoforestParentTable_readout

theorem d7Stage1Pair56CoforestChildTable_readout_closed :
    d7Stage1Pair56CoforestChildTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.leaf1,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.leaf2,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.leaf3,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.mate] :=
  d7Stage1Pair56CoforestChildTable_readout

theorem d7Stage1Pair56CoforestParentStepTable_readout_closed :
    d7Stage1Pair56CoforestParentStepTable =
      [_root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.hub,
        _root_.EvenV11.TypeA.RootHubThreeLeafCoforestVertex.root] :=
  d7Stage1Pair56CoforestParentStepTable_readout

theorem d7Stage1Pair56CoforestRankTable_readout_closed :
    d7Stage1Pair56CoforestRankTable = [0, 1, 2, 2, 2, 1] :=
  d7Stage1Pair56CoforestRankTable_readout

theorem d7Stage1TripleCoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage1TripleCoforestDescendantCut
      d7Stage1TripleCoforestParent
      d7Stage1TripleCoforestChild :=
  d7Stage1TripleCoforestParentMapBoundary

theorem d7Stage1TripleCoforestIncidence_eq_ite_closed
    (cut edge : D7Stage1TripleCoforestEdge) :
    @parentMapIncidence
        D7Stage1TripleCoforestVertex D7Stage1TripleCoforestEdge
        d7Stage1TripleCoforestDescendantCut
        d7Stage1TripleCoforestDescendantCutDecidable
        d7Stage1TripleCoforestParent
        d7Stage1TripleCoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage1TripleCoforestIncidence_eq_ite cut edge

theorem d7Stage1TripleCoforestIncidence_self_closed
    (edge : D7Stage1TripleCoforestEdge) :
    @parentMapIncidence
        D7Stage1TripleCoforestVertex D7Stage1TripleCoforestEdge
        d7Stage1TripleCoforestDescendantCut
        d7Stage1TripleCoforestDescendantCutDecidable
        d7Stage1TripleCoforestParent
        d7Stage1TripleCoforestChild edge edge = 1 :=
  d7Stage1TripleCoforestIncidence_self edge

theorem d7Stage1TripleCoforestIncidence_ne_closed
    {cut edge : D7Stage1TripleCoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage1TripleCoforestVertex D7Stage1TripleCoforestEdge
        d7Stage1TripleCoforestDescendantCut
        d7Stage1TripleCoforestDescendantCutDecidable
        d7Stage1TripleCoforestParent
        d7Stage1TripleCoforestChild cut edge = 0 :=
  d7Stage1TripleCoforestIncidence_ne hne

theorem d7Stage1TripleCoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage1TripleCoforestParentStep
        d7Stage1TripleCoforestChild)
      d7Stage1TripleCoforestParent
      d7Stage1TripleCoforestChild :=
  d7Stage1TripleCoforestIteratedParentMapBoundary

theorem d7Stage1Pair34CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage1Pair34CoforestDescendantCut
      d7Stage1Pair34CoforestParent
      d7Stage1Pair34CoforestChild :=
  d7Stage1Pair34CoforestParentMapBoundary

theorem d7Stage1Pair34CoforestIncidence_eq_ite_closed
    (cut edge : D7Stage1Pair34CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair34CoforestVertex D7Stage1Pair34CoforestEdge
        d7Stage1Pair34CoforestDescendantCut
        d7Stage1Pair34CoforestDescendantCutDecidable
        d7Stage1Pair34CoforestParent
        d7Stage1Pair34CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage1Pair34CoforestIncidence_eq_ite cut edge

theorem d7Stage1Pair34CoforestIncidence_self_closed
    (edge : D7Stage1Pair34CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair34CoforestVertex D7Stage1Pair34CoforestEdge
        d7Stage1Pair34CoforestDescendantCut
        d7Stage1Pair34CoforestDescendantCutDecidable
        d7Stage1Pair34CoforestParent
        d7Stage1Pair34CoforestChild edge edge = 1 :=
  d7Stage1Pair34CoforestIncidence_self edge

theorem d7Stage1Pair34CoforestIncidence_ne_closed
    {cut edge : D7Stage1Pair34CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage1Pair34CoforestVertex D7Stage1Pair34CoforestEdge
        d7Stage1Pair34CoforestDescendantCut
        d7Stage1Pair34CoforestDescendantCutDecidable
        d7Stage1Pair34CoforestParent
        d7Stage1Pair34CoforestChild cut edge = 0 :=
  d7Stage1Pair34CoforestIncidence_ne hne

theorem d7Stage1Pair34CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage1Pair34CoforestParentStep
        d7Stage1Pair34CoforestChild)
      d7Stage1Pair34CoforestParent
      d7Stage1Pair34CoforestChild :=
  d7Stage1Pair34CoforestIteratedParentMapBoundary

theorem d7Stage1Pair56CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage1Pair56CoforestDescendantCut
      d7Stage1Pair56CoforestParent
      d7Stage1Pair56CoforestChild :=
  d7Stage1Pair56CoforestParentMapBoundary

theorem d7Stage1Pair56CoforestIncidence_eq_ite_closed
    (cut edge : D7Stage1Pair56CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair56CoforestVertex D7Stage1Pair56CoforestEdge
        d7Stage1Pair56CoforestDescendantCut
        d7Stage1Pair56CoforestDescendantCutDecidable
        d7Stage1Pair56CoforestParent
        d7Stage1Pair56CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage1Pair56CoforestIncidence_eq_ite cut edge

theorem d7Stage1Pair56CoforestIncidence_self_closed
    (edge : D7Stage1Pair56CoforestEdge) :
    @parentMapIncidence
        D7Stage1Pair56CoforestVertex D7Stage1Pair56CoforestEdge
        d7Stage1Pair56CoforestDescendantCut
        d7Stage1Pair56CoforestDescendantCutDecidable
        d7Stage1Pair56CoforestParent
        d7Stage1Pair56CoforestChild edge edge = 1 :=
  d7Stage1Pair56CoforestIncidence_self edge

theorem d7Stage1Pair56CoforestIncidence_ne_closed
    {cut edge : D7Stage1Pair56CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage1Pair56CoforestVertex D7Stage1Pair56CoforestEdge
        d7Stage1Pair56CoforestDescendantCut
        d7Stage1Pair56CoforestDescendantCutDecidable
        d7Stage1Pair56CoforestParent
        d7Stage1Pair56CoforestChild cut edge = 0 :=
  d7Stage1Pair56CoforestIncidence_ne hne

theorem d7Stage1Pair56CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage1Pair56CoforestParentStep
        d7Stage1Pair56CoforestChild)
      d7Stage1Pair56CoforestParent
      d7Stage1Pair56CoforestChild :=
  d7Stage1Pair56CoforestIteratedParentMapBoundary

theorem d7Stage2CoforestIncidence_eq_ite_closed
    (cut edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage2CoforestIncidence_eq_ite cut edge

theorem d7Stage2CoforestIncidence_self_closed
    (edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild edge edge = 1 :=
  d7Stage2CoforestIncidence_self edge

theorem d7Stage2CoforestIncidence_ne_closed
    {cut edge : D7Stage2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge = 0 :=
  d7Stage2CoforestIncidence_ne hne

theorem d7Stage2CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut d7Stage2CoforestParentStep
        d7Stage2CoforestChild)
      d7Stage2CoforestParent
      d7Stage2CoforestChild :=
  d7Stage2CoforestIteratedParentMapBoundary

theorem d7Stage2CoforestIncidenceCertificate_boundary_closed :
    ParentMapBoundary
      d7Stage2CoforestDescendantCut
      d7Stage2CoforestParent
      d7Stage2CoforestChild :=
  d7Stage2CoforestIncidenceCertificate_boundary

theorem d7Stage2CoforestIncidenceCertificate_eq_ite_closed
    (cut edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage2CoforestIncidenceCertificate_eq_ite cut edge

theorem d7Stage2CoforestIncidenceCertificate_self_closed
    (edge : D7Stage2CoforestEdge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild edge edge = 1 :=
  d7Stage2CoforestIncidenceCertificate_self edge

theorem d7Stage2CoforestIncidenceCertificate_ne_closed
    {cut edge : D7Stage2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2CoforestVertex D7Stage2CoforestEdge
        d7Stage2CoforestDescendantCut
        d7Stage2CoforestDescendantCutDecidable
        d7Stage2CoforestParent d7Stage2CoforestChild cut edge = 0 :=
  d7Stage2CoforestIncidenceCertificate_ne hne

theorem d7Stage2Packet134Color34CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage2Packet134Color34CoforestDescendantCut
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild :=
  d7Stage2Packet134Color34CoforestParentMapBoundary

theorem d7Stage2Packet134Color34CoforestIncidence_eq_ite_closed
    (cut edge : D7Stage2Packet134Color34CoforestEdge) :
    @parentMapIncidence
        D7Stage2Packet134Color34CoforestVertex
        D7Stage2Packet134Color34CoforestEdge
        d7Stage2Packet134Color34CoforestDescendantCut
        d7Stage2Packet134Color34CoforestDescendantCutDecidable
        d7Stage2Packet134Color34CoforestParent
        d7Stage2Packet134Color34CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage2Packet134Color34CoforestIncidence_eq_ite cut edge

theorem d7Stage2Packet134Color34CoforestIncidence_self_closed
    (edge : D7Stage2Packet134Color34CoforestEdge) :
    @parentMapIncidence
        D7Stage2Packet134Color34CoforestVertex
        D7Stage2Packet134Color34CoforestEdge
        d7Stage2Packet134Color34CoforestDescendantCut
        d7Stage2Packet134Color34CoforestDescendantCutDecidable
        d7Stage2Packet134Color34CoforestParent
        d7Stage2Packet134Color34CoforestChild edge edge = 1 :=
  d7Stage2Packet134Color34CoforestIncidence_self edge

theorem d7Stage2Packet134Color34CoforestIncidence_ne_closed
    {cut edge : D7Stage2Packet134Color34CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Packet134Color34CoforestVertex
        D7Stage2Packet134Color34CoforestEdge
        d7Stage2Packet134Color34CoforestDescendantCut
        d7Stage2Packet134Color34CoforestDescendantCutDecidable
        d7Stage2Packet134Color34CoforestParent
        d7Stage2Packet134Color34CoforestChild cut edge = 0 :=
  d7Stage2Packet134Color34CoforestIncidence_ne hne

theorem d7Stage2Packet134Color34CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Packet134Color34CoforestParentStep
        d7Stage2Packet134Color34CoforestChild)
      d7Stage2Packet134Color34CoforestParent
      d7Stage2Packet134Color34CoforestChild :=
  d7Stage2Packet134Color34CoforestIteratedParentMapBoundary

theorem d7Stage2Pair02Color0CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage2Pair02Color0CoforestDescendantCut
      d7Stage2Pair02Color0CoforestParent
      d7Stage2Pair02Color0CoforestChild :=
  d7Stage2Pair02Color0CoforestParentMapBoundary

theorem d7Stage2Pair02Color0CoforestIncidence_eq_ite_closed
    (cut edge : D7Stage2Pair02Color0CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color0CoforestVertex
        D7Stage2Pair02Color0CoforestEdge
        d7Stage2Pair02Color0CoforestDescendantCut
        d7Stage2Pair02Color0CoforestDescendantCutDecidable
        d7Stage2Pair02Color0CoforestParent
        d7Stage2Pair02Color0CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage2Pair02Color0CoforestIncidence_eq_ite cut edge

theorem d7Stage2Pair02Color0CoforestIncidence_self_closed
    (edge : D7Stage2Pair02Color0CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color0CoforestVertex
        D7Stage2Pair02Color0CoforestEdge
        d7Stage2Pair02Color0CoforestDescendantCut
        d7Stage2Pair02Color0CoforestDescendantCutDecidable
        d7Stage2Pair02Color0CoforestParent
        d7Stage2Pair02Color0CoforestChild edge edge = 1 :=
  d7Stage2Pair02Color0CoforestIncidence_self edge

theorem d7Stage2Pair02Color0CoforestIncidence_ne_closed
    {cut edge : D7Stage2Pair02Color0CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Pair02Color0CoforestVertex
        D7Stage2Pair02Color0CoforestEdge
        d7Stage2Pair02Color0CoforestDescendantCut
        d7Stage2Pair02Color0CoforestDescendantCutDecidable
        d7Stage2Pair02Color0CoforestParent
        d7Stage2Pair02Color0CoforestChild cut edge = 0 :=
  d7Stage2Pair02Color0CoforestIncidence_ne hne

theorem d7Stage2Pair02Color0CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Pair02Color0CoforestParentStep
        d7Stage2Pair02Color0CoforestChild)
      d7Stage2Pair02Color0CoforestParent
      d7Stage2Pair02Color0CoforestChild :=
  d7Stage2Pair02Color0CoforestIteratedParentMapBoundary

theorem d7Stage2Pair02Color2CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage2Pair02Color2CoforestDescendantCut
      d7Stage2Pair02Color2CoforestParent
      d7Stage2Pair02Color2CoforestChild :=
  d7Stage2Pair02Color2CoforestParentMapBoundary

theorem d7Stage2Pair02Color2CoforestIncidence_eq_ite_closed
    (cut edge : D7Stage2Pair02Color2CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color2CoforestVertex
        D7Stage2Pair02Color2CoforestEdge
        d7Stage2Pair02Color2CoforestDescendantCut
        d7Stage2Pair02Color2CoforestDescendantCutDecidable
        d7Stage2Pair02Color2CoforestParent
        d7Stage2Pair02Color2CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage2Pair02Color2CoforestIncidence_eq_ite cut edge

theorem d7Stage2Pair02Color2CoforestIncidence_self_closed
    (edge : D7Stage2Pair02Color2CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair02Color2CoforestVertex
        D7Stage2Pair02Color2CoforestEdge
        d7Stage2Pair02Color2CoforestDescendantCut
        d7Stage2Pair02Color2CoforestDescendantCutDecidable
        d7Stage2Pair02Color2CoforestParent
        d7Stage2Pair02Color2CoforestChild edge edge = 1 :=
  d7Stage2Pair02Color2CoforestIncidence_self edge

theorem d7Stage2Pair02Color2CoforestIncidence_ne_closed
    {cut edge : D7Stage2Pair02Color2CoforestEdge} (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Pair02Color2CoforestVertex
        D7Stage2Pair02Color2CoforestEdge
        d7Stage2Pair02Color2CoforestDescendantCut
        d7Stage2Pair02Color2CoforestDescendantCutDecidable
        d7Stage2Pair02Color2CoforestParent
        d7Stage2Pair02Color2CoforestChild cut edge = 0 :=
  d7Stage2Pair02Color2CoforestIncidence_ne hne

theorem d7Stage2Pair02Color2CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Pair02Color2CoforestParentStep
        d7Stage2Pair02Color2CoforestChild)
      d7Stage2Pair02Color2CoforestParent
      d7Stage2Pair02Color2CoforestChild :=
  d7Stage2Pair02Color2CoforestIteratedParentMapBoundary

theorem d7Stage2Pair56Color56CoforestParentMapBoundary_closed :
    ParentMapBoundary
      d7Stage2Pair56Color56CoforestDescendantCut
      d7Stage2Pair56Color56CoforestParent
      d7Stage2Pair56Color56CoforestChild :=
  d7Stage2Pair56Color56CoforestParentMapBoundary

theorem d7Stage2Pair56Color56CoforestIncidence_eq_ite_closed
    (cut edge : D7Stage2Pair56Color56CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair56Color56CoforestVertex
        D7Stage2Pair56Color56CoforestEdge
        d7Stage2Pair56Color56CoforestDescendantCut
        d7Stage2Pair56Color56CoforestDescendantCutDecidable
        d7Stage2Pair56Color56CoforestParent
        d7Stage2Pair56Color56CoforestChild cut edge =
      if cut = edge then (1 : Int) else 0 :=
  d7Stage2Pair56Color56CoforestIncidence_eq_ite cut edge

theorem d7Stage2Pair56Color56CoforestIncidence_self_closed
    (edge : D7Stage2Pair56Color56CoforestEdge) :
    @parentMapIncidence
        D7Stage2Pair56Color56CoforestVertex
        D7Stage2Pair56Color56CoforestEdge
        d7Stage2Pair56Color56CoforestDescendantCut
        d7Stage2Pair56Color56CoforestDescendantCutDecidable
        d7Stage2Pair56Color56CoforestParent
        d7Stage2Pair56Color56CoforestChild edge edge = 1 :=
  d7Stage2Pair56Color56CoforestIncidence_self edge

theorem d7Stage2Pair56Color56CoforestIncidence_ne_closed
    {cut edge : D7Stage2Pair56Color56CoforestEdge}
    (hne : cut ≠ edge) :
    @parentMapIncidence
        D7Stage2Pair56Color56CoforestVertex
        D7Stage2Pair56Color56CoforestEdge
        d7Stage2Pair56Color56CoforestDescendantCut
        d7Stage2Pair56Color56CoforestDescendantCutDecidable
        d7Stage2Pair56Color56CoforestParent
        d7Stage2Pair56Color56CoforestChild cut edge = 0 :=
  d7Stage2Pair56Color56CoforestIncidence_ne hne

theorem d7Stage2Pair56Color56CoforestIteratedParentMapBoundary_closed :
    ParentMapBoundary
      (iteratedParentDescendantCut
        d7Stage2Pair56Color56CoforestParentStep
        d7Stage2Pair56Color56CoforestChild)
      d7Stage2Pair56Color56CoforestParent
      d7Stage2Pair56Color56CoforestChild :=
  d7Stage2Pair56Color56CoforestIteratedParentMapBoundary

theorem d5ForestClosingAudit_closed :
    FiniteAudit.d5ForestClosingAuditBool = true :=
  d5ForestClosingAudit

theorem d7ForestClosingAudit_closed :
    FiniteAudit.d7ForestClosingAuditBool = true :=
  d7ForestClosingAudit

theorem d5SupportAudit_closed :
    FiniteAudit.d5SupportAuditBool = true :=
  d5SupportAudit

theorem d7SupportAudit_closed :
    FiniteAudit.d7SupportAuditBool = true :=
  d7SupportAudit

theorem d5ReservePlaneAudit_closed :
    FiniteAudit.d5ReservePlaneAuditBool = true :=
  d5ReservePlaneAudit

theorem d7ReservePlaneAudit_closed :
    FiniteAudit.d7ReservePlaneAuditBool = true :=
  d7ReservePlaneAudit

theorem foldedTerminalWordAudit_closed :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6)) :=
  foldedTerminalWordAudit

theorem v28FiniteAuditSummary_closed :
    FiniteAudit.d5ForestClosingAuditBool = true ∧
    FiniteAudit.d7ForestClosingAuditBool = true ∧
    FiniteAudit.d5SupportAuditBool = true ∧
    FiniteAudit.d7SupportAuditBool = true ∧
    FiniteAudit.d5ReservePlaneAuditBool = true ∧
    FiniteAudit.d7ReservePlaneAuditBool = true ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6)) :=
  v28FiniteAuditSummary

theorem d5HighEvenAnchorAudit_closed :
    FiniteAuditBridge.d5HighEvenAnchorAuditBool = true :=
  d5HighEvenAnchorAudit

theorem d7HighEvenAnchorAudit_closed :
    FiniteAuditBridge.d7HighEvenAnchorAuditBool = true :=
  d7HighEvenAnchorAudit

theorem highEvenAnchorDimensions_nodup_closed :
    FiniteAuditBridge.highEvenAnchorDimensions.Nodup :=
  highEvenAnchorDimensions_nodup

theorem highEvenAnchorDimensionsAudit_closed :
    FiniteAuditBridge.highEvenAnchorDimensionsAuditBool = true :=
  highEvenAnchorDimensionsAudit

theorem v28FiniteInputBridgeAudit_closed :
    FiniteAuditBridge.highEvenAnchorDimensionsAuditBool = true ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6)) :=
  v28FiniteInputBridgeAudit

theorem d5CoforestRowsRootedAudit_holds_closed :
    TypeA.d5CoforestRowsRootedAudit :=
  d5CoforestRowsRootedAudit_holds

theorem d5CoforestRowsIncidenceAudit_holds_closed :
    TypeA.d5CoforestRowsIncidenceAudit :=
  d5CoforestRowsIncidenceAudit_holds

theorem d7Stage12CoforestRowsRootedAudit_holds_closed :
    TypeA.d7Stage12CoforestRowsRootedAudit :=
  d7Stage12CoforestRowsRootedAudit_holds

theorem d7Stage12CoforestRowsIncidenceAudit_holds_closed :
    TypeA.d7Stage12CoforestRowsIncidenceAudit :=
  d7Stage12CoforestRowsIncidenceAudit_holds

theorem v28FiniteInputCoforestAudit_holds_closed :
    TypeA.v28FiniteInputCoforestAudit :=
  v28FiniteInputCoforestAudit_holds

theorem highEvenProjectionKernelInput_holds_closed :
    HighEvenProjectionKernelInput :=
  highEvenProjectionKernelInput_holds

theorem highEvenGuideLocalityInput_holds_closed :
    HighEvenGuideLocalityInput :=
  highEvenGuideLocalityInput_holds

theorem highEvenFiniteAnchorInput_holds_closed :
    HighEvenFiniteAnchorInput :=
  highEvenFiniteAnchorInput_holds

theorem highEvenSuccessorBridgeInput_holds_closed :
    HighEvenSuccessorBridgeInput :=
  highEvenSuccessorBridgeInput_holds

theorem finalReturnCoreInput_holds_closed :
    FinalReturnCoreInput :=
  finalReturnCoreInput_holds

theorem finalWordCoreInput_holds_closed :
    FinalWordCoreInput :=
  finalWordCoreInput_holds

theorem finalTerminalInput_holds_closed :
    FinalTerminalInput :=
  finalTerminalInput_holds

theorem finalEndpointInput_holds_closed :
    FinalEndpointInput :=
  finalEndpointInput_holds

theorem finalHighEvenInput_holds_closed :
    FinalHighEvenInput :=
  finalHighEvenInput_holds

theorem finalInductionInterfaceInput_holds_closed :
    FinalInductionInterfaceInput :=
  finalInductionInterfaceInput_holds

theorem ordinaryBaseTwoRange_closed
    {m : Nat} (hm : EvenModulusRange m) :
    OrdinaryDimensionRange 2 m :=
  ordinaryBaseTwoRange hm

theorem ordinaryBaseThreeRange_closed
    {m : Nat} (hm : EvenModulusRange m) :
    OrdinaryDimensionRange 3 m :=
  ordinaryBaseThreeRange hm

theorem d5ResetMarkedRange_closed :
    MarkedDimensionRange 5 4 :=
  d5ResetMarkedRange

theorem rankThreeMarkedRange4_closed :
    MarkedDimensionRange 7 4 :=
  rankThreeMarkedRange4

theorem rankThreeMarkedRange6_closed :
    MarkedDimensionRange 7 6 :=
  rankThreeMarkedRange6

theorem markedRange_forget_closed
    {d m : Nat} (h : MarkedDimensionRange d m) :
    OrdinaryDimensionRange d m :=
  markedRange_forget h

theorem evenStepParentOrdinaryRange_closed
    {d a m : Nat} (h : OrdinaryDimensionRange d m)
    (hd : d = 2 * a) (hmin : 4 ≤ d) :
    OrdinaryDimensionRange a m :=
  evenStepParentOrdinaryRange h hd hmin

theorem markedEvenStepParentOrdinaryRange_closed
    {d a m : Nat} (h : MarkedDimensionRange d m)
    (hd : d = 2 * a) (hmin : 4 ≤ d) :
    OrdinaryDimensionRange a m :=
  markedEvenStepParentOrdinaryRange h hd hmin

theorem endpointParentMarkedRange_closed
    {d b m : Nat} (hd : d = 2 * b + 1)
    (hb : 4 ≤ b) (hm : EvenModulusRange m) (hmle : m ≤ d) :
    MarkedDimensionRange b m :=
  endpointParentMarkedRange hd hb hm hmle

theorem oddLowRangeCase_of_range_closed
    {d m : Nat}
    (hdOdd : ∃ b : Nat, d = 2 * b + 1)
    (hmin : 5 ≤ d) (hm : EvenModulusRange m) (hmle : m ≤ d) :
    OddLowRangeCase d m :=
  oddLowRangeCase_of_range hdOdd hmin hm hmle

theorem oddBranchRangeCase_of_range_closed
    {d m : Nat}
    (hdOdd : ∃ b : Nat, d = 2 * b + 1)
    (hmin : 5 ≤ d) (hm : EvenModulusRange m) :
    OddBranchRangeCase d m :=
  oddBranchRangeCase_of_range hdOdd hmin hm

theorem finalRangeInput_holds_closed :
    FinalRangeInput :=
  finalRangeInput_holds

theorem finalInductionRangeBridgeInput_holds_closed :
    FinalInductionRangeBridgeInput :=
  finalInductionRangeBridgeInput_holds

theorem finalInductionScheme_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (range : FinalRangeInput)
    (arrows : FinalInductionArrowInput Ordinary Marked) :
    (∀ d m : Nat, OrdinaryDimensionRange d m → Ordinary d m) ∧
      (∀ d m : Nat, MarkedDimensionRange d m → Marked d m) :=
  finalInductionScheme range arrows

theorem finalInductionSchemeBridgeInput_holds_closed :
    FinalInductionSchemeBridgeInput :=
  finalInductionSchemeBridgeInput_holds

theorem ordinaryConclusionFromFinalInductionScheme_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (range : FinalRangeInput)
    (arrows : FinalInductionArrowInput Ordinary Marked)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Ordinary d m :=
  ordinaryConclusionFromFinalInductionScheme range arrows hRange

theorem markedConclusionFromFinalInductionScheme_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (range : FinalRangeInput)
    (arrows : FinalInductionArrowInput Ordinary Marked)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Marked d m :=
  markedConclusionFromFinalInductionScheme range arrows hRange

theorem finalSchemeProjectionInput_holds_closed :
    FinalSchemeProjectionInput :=
  finalSchemeProjectionInput_holds

theorem finalConstructionArrowBridgeInput_of_arrows_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (arrows : FinalInductionArrowInput Ordinary Marked) :
    FinalConstructionArrowBridgeInput Ordinary Marked :=
  finalConstructionArrowBridgeInput_of_arrows arrows

theorem ordinaryConclusionFromConstructionArrows_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalConstructionArrowBridgeInput Ordinary Marked)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Ordinary d m :=
  ordinaryConclusionFromConstructionArrows input hRange

theorem markedConclusionFromConstructionArrows_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalConstructionArrowBridgeInput Ordinary Marked)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Marked d m :=
  markedConclusionFromConstructionArrows input hRange

theorem finalArrowObligationInput_of_finalInductionArrows_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (arrows : FinalInductionArrowInput Ordinary Marked) :
    FinalArrowObligationInput Ordinary Marked :=
  finalArrowObligationInput_of_finalInductionArrows arrows

theorem finalInductionArrowInput_of_arrowObligationInput_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked) :
    FinalInductionArrowInput Ordinary Marked :=
  finalInductionArrowInput_of_arrowObligationInput input

theorem finalConstructionArrowBridgeInput_of_arrowObligationInput_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked) :
    FinalConstructionArrowBridgeInput Ordinary Marked :=
  finalConstructionArrowBridgeInput_of_arrowObligationInput input

theorem ordinaryConclusionFromArrowObligations_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Ordinary d m :=
  ordinaryConclusionFromArrowObligations input hRange

theorem markedConclusionFromArrowObligations_closed
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Marked d m :=
  markedConclusionFromArrowObligations input hRange

theorem finalTargetMarkedToOrdinary_closed
    {d m : Nat} :
    FinalMarkedTarget d m → FinalOrdinaryTarget d m :=
  finalTargetMarkedToOrdinary

theorem finalTargetBaseArrowObligations_of_targetBase_closed
    (base : FinalTargetBaseObligations) :
    FinalBaseArrowObligations FinalOrdinaryTarget FinalMarkedTarget :=
  finalTargetBaseArrowObligations_of_targetBase base

theorem finalTargetSuccessorArrowObligations_of_targetGrowth_closed
    (growth : FinalTargetGrowthObligations) :
    FinalSuccessorArrowObligations FinalOrdinaryTarget FinalMarkedTarget :=
  finalTargetSuccessorArrowObligations_of_targetGrowth growth

theorem finalTargetArrowObligationInput_of_targetObligations_closed
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations) :
    FinalArrowObligationInput FinalOrdinaryTarget FinalMarkedTarget :=
  finalTargetArrowObligationInput_of_targetObligations base growth

theorem finalTargetTorusConclusionFromTargetObligations_closed
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromTargetObligations base growth hRange

theorem finalTargetMarkedTorusConclusionFromTargetObligations_closed
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromTargetObligations
    base growth hRange

theorem finalTargetCayleyConclusionFromTargetObligations_closed
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromTargetObligations
    base growth hRange

theorem finalTargetOrdinaryTwoBase_closed
    {m : Nat} (hm : EvenModulusRange m) :
    FinalOrdinaryTarget 2 m :=
  finalTargetOrdinaryTwoBase hm

theorem finalTargetD2BaseInput_holds_closed :
    FinalTargetD2BaseInput :=
  finalTargetD2BaseInput_holds

theorem finalTargetBaseObligations_of_remainingBase_closed
    (remaining : FinalRemainingTargetBaseObligations) :
    FinalTargetBaseObligations :=
  finalTargetBaseObligations_of_remainingBase remaining

theorem finalTargetTorusConclusionFromRemainingBaseAndGrowth_closed
    (remaining : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromRemainingBaseAndGrowth
    remaining growth hRange

theorem finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowth_closed
    (remaining : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowth
    remaining growth hRange

theorem finalTargetCayleyConclusionFromRemainingBaseAndGrowth_closed
    (remaining : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromRemainingBaseAndGrowth
    remaining growth hRange

theorem finalTargetClosedGrowthLocalInputs_holds_closed :
    FinalTargetClosedGrowthLocalInputs :=
  finalTargetClosedGrowthLocalInputs_holds

theorem finalTargetGrowthObligations_of_remainingGrowthArrows_closed
    (remaining : FinalRemainingTargetGrowthArrows) :
    FinalTargetGrowthObligations :=
  finalTargetGrowthObligations_of_remainingGrowthArrows remaining

theorem finalTargetGrowthAssemblyInput_of_remainingGrowthArrows_closed
    (remaining : FinalRemainingTargetGrowthArrows) :
    FinalTargetGrowthAssemblyInput :=
  finalTargetGrowthAssemblyInput_of_remainingGrowthArrows remaining

theorem finalTargetGrowthObligations_of_growthAssemblyInput_closed
    (input : FinalTargetGrowthAssemblyInput) :
    FinalTargetGrowthObligations :=
  finalTargetGrowthObligations_of_growthAssemblyInput input

theorem finalTargetTorusConclusionFromRemainingBaseAndGrowthArrows_closed
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromRemainingBaseAndGrowthArrows
    base growth hRange

theorem finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthArrows_closed
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthArrows
    base growth hRange

theorem finalTargetCayleyConclusionFromRemainingBaseAndGrowthArrows_closed
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromRemainingBaseAndGrowthArrows
    base growth hRange

theorem finalTargetTorusConclusionFromRemainingBaseAndGrowthAssembly_closed
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromRemainingBaseAndGrowthAssembly
    base growth hRange

theorem finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthAssembly_closed
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthAssembly
    base growth hRange

theorem finalTargetCayleyConclusionFromRemainingBaseAndGrowthAssembly_closed
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromRemainingBaseAndGrowthAssembly
    base growth hRange

theorem finalLowMarkedBaseClosedInputs_holds_closed :
    FinalLowMarkedBaseClosedInputs :=
  finalLowMarkedBaseClosedInputs_holds

theorem finalLowMarkedBaseTerminalTrace4Cycle_closed
    (input : FinalLowMarkedBaseClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4) :=
  finalLowMarkedBaseTerminalTrace4Cycle input

theorem finalLowMarkedBaseTerminalTrace6Cycle_closed
    (input : FinalLowMarkedBaseClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6) :=
  finalLowMarkedBaseTerminalTrace6Cycle input

theorem finalLowMarkedBaseTerminalReset4Cycle_closed
    (input : FinalLowMarkedBaseClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  finalLowMarkedBaseTerminalReset4Cycle input

theorem finalLowMarkedBaseEndpointInput_closed
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalEndpointInput :=
  finalLowMarkedBaseEndpointInput input

theorem finalLowMarkedBaseObligations_of_promotions_closed
    (promotions : FinalLowMarkedBasePromotions) :
    FinalLowMarkedBaseObligations :=
  finalLowMarkedBaseObligations_of_promotions promotions

theorem finalRemainingBase_of_ordinaryThreeAndLowMarkedBase_closed
    (ordinary : FinalOrdinaryThreeBaseObligation)
    (low : FinalLowMarkedBaseObligations) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_ordinaryThreeAndLowMarkedBase
    ordinary low

theorem finalRemainingBase_of_ordinaryThreeAndLowPromotions_closed
    (ordinary : FinalOrdinaryThreeBaseObligation)
    (promotions : FinalLowMarkedBasePromotions) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_ordinaryThreeAndLowPromotions
    ordinary promotions

theorem finalRemainingBase_of_basePromotionAssemblyInput_closed
    (input : FinalTargetBasePromotionAssemblyInput) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_basePromotionAssemblyInput input

theorem finalTargetTorus_from_basePromotionGrowthArrows_closed
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionGrowthArrows
    base growth hRange

theorem finalTargetMarkedTorus_from_basePromotionGrowthArrows_closed
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionGrowthArrows
    base growth hRange

theorem finalTargetCayley_from_basePromotionGrowthArrows_closed
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionGrowthArrows
    base growth hRange

theorem finalTargetTorus_from_basePromotionGrowthAssembly_closed
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionGrowthAssembly
    base growth hRange

theorem finalTargetMarkedTorus_from_basePromotionGrowthAssembly_closed
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionGrowthAssembly
    base growth hRange

theorem finalTargetCayley_from_basePromotionGrowthAssembly_closed
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionGrowthAssembly
    base growth hRange

theorem finalTargetEvenPhaseDoubling_closed
    {a m : Nat} (ha : 2 ≤ a) (hm : EvenModulusRange m)
    (parent : FinalOrdinaryTarget a m) :
    FinalMarkedTarget (2 * a) m :=
  finalTargetEvenPhaseDoubling ha hm parent

theorem finalRemainingTargetGrowthArrows_of_postPhase_closed
    (remaining : FinalRemainingTargetPostPhaseGrowthArrows) :
    FinalRemainingTargetGrowthArrows :=
  finalRemainingTargetGrowthArrows_of_postPhase remaining

theorem finalTargetPostPhaseGrowthAssemblyInput_of_remaining_closed
    (remaining : FinalRemainingTargetPostPhaseGrowthArrows) :
    FinalTargetPostPhaseGrowthAssemblyInput :=
  finalTargetPostPhaseGrowthAssemblyInput_of_remaining remaining

theorem finalTargetGrowthAssemblyInput_of_postPhase_closed
    (input : FinalTargetPostPhaseGrowthAssemblyInput) :
    FinalTargetGrowthAssemblyInput :=
  finalTargetGrowthAssemblyInput_of_postPhase input

theorem finalTargetTorus_from_basePromotionsPostPhaseGrowth_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetPostPhaseGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionsPostPhaseGrowth
    base growth hRange

theorem finalTargetMarkedTorus_from_basePromotionsPostPhaseGrowth_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetPostPhaseGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionsPostPhaseGrowth
    base growth hRange

theorem finalTargetCayley_from_basePromotionsPostPhaseGrowth_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetPostPhaseGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionsPostPhaseGrowth
    base growth hRange

theorem finalTargetTorus_from_basePromotionsPostPhaseAssembly_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetPostPhaseGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionsPostPhaseAssembly
    base growth hRange

theorem finalTargetMarkedTorus_from_basePromotionsPostPhaseAssembly_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetPostPhaseGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionsPostPhaseAssembly
    base growth hRange

theorem finalTargetCayley_from_basePromotionsPostPhaseAssembly_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetPostPhaseGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionsPostPhaseAssembly
    base growth hRange

theorem finalD3EvenBaseClosedInputs_holds_closed :
    FinalD3EvenBaseClosedInputs :=
  finalD3EvenBaseClosedInputs_holds

theorem finalD3EvenBaseOrdinaryRange_closed
    (input : FinalD3EvenBaseClosedInputs)
    {m : Nat} (hm : EvenModulusRange m) :
    OrdinaryDimensionRange 3 m :=
  finalD3EvenBaseOrdinaryRange input hm

theorem finalD3EvenBaseReturnCriterionInput_closed
    (input : FinalD3EvenBaseClosedInputs) :
    ∀ {Color Direction RootState : Type} {m : Nat} [NeZero m]
      {S : Shared.RootFlatSchedule Color Direction RootState m},
      S.rowLatin →
      S.layerBijective →
      S.returnsSingleCycle →
      Shared.RootFlatReturnCriterion Color Direction RootState m :=
  finalD3EvenBaseReturnCriterionInput input

theorem finalD3EvenBaseLayeredHamiltonianInput_closed
    (input : FinalD3EvenBaseClosedInputs) :
    ∀ {Color Direction RootState : Type} {m : Nat} [NeZero m]
      {S : Shared.RootFlatSchedule Color Direction RootState m},
      S.rowLatin →
      S.layerBijective →
      S.returnsSingleCycle →
      Shared.RootFlatLayeredHamiltonDecomposition
        Color Direction RootState m :=
  finalD3EvenBaseLayeredHamiltonianInput input

theorem finalOrdinaryThreeBaseObligation_of_d3Promotion_closed
    (promotion : FinalD3EvenBasePromotion) :
    FinalOrdinaryThreeBaseObligation :=
  finalOrdinaryThreeBaseObligation_of_d3Promotion promotion

theorem finalTargetBasePromotionAssemblyInput_of_basePromotions_closed
    (input : FinalBasePromotionAssemblyInput) :
    FinalTargetBasePromotionAssemblyInput :=
  finalTargetBasePromotionAssemblyInput_of_basePromotions input

theorem finalRemainingBase_of_basePromotions_closed
    (input : FinalBasePromotionAssemblyInput) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_basePromotions input

theorem finalTargetTorus_from_basePromotionsGrowthArrows_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionsGrowthArrows
    base growth hRange

theorem finalTargetMarkedTorus_from_basePromotionsGrowthArrows_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionsGrowthArrows
    base growth hRange

theorem finalTargetCayley_from_basePromotionsGrowthArrows_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionsGrowthArrows
    base growth hRange

theorem finalTargetTorus_from_basePromotionsGrowthAssembly_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionsGrowthAssembly
    base growth hRange

theorem finalTargetMarkedTorus_from_basePromotionsGrowthAssembly_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionsGrowthAssembly
    base growth hRange

theorem finalTargetCayley_from_basePromotionsGrowthAssembly_closed
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionsGrowthAssembly
    base growth hRange

theorem finalBasePromotionAssemblyInput_of_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations) :
    FinalBasePromotionAssemblyInput :=
  finalBasePromotionAssemblyInput_of_exactRemaining remaining

theorem finalPostPhaseGrowthAssemblyInput_of_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetPostPhaseGrowthAssemblyInput :=
  finalPostPhaseGrowthAssemblyInput_of_exactRemaining remaining

theorem finalTargetGrowthAssemblyInput_of_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetGrowthAssemblyInput :=
  finalTargetGrowthAssemblyInput_of_exactRemaining remaining

theorem finalRemainingBase_of_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_exactRemaining remaining

theorem finalRemainingTargetGrowthArrows_of_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations) :
    FinalRemainingTargetGrowthArrows :=
  finalRemainingTargetGrowthArrows_of_exactRemaining remaining

theorem finalTargetBaseObligations_of_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetBaseObligations :=
  finalTargetBaseObligations_of_exactRemaining remaining

theorem finalTargetGrowthObligations_of_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetGrowthObligations :=
  finalTargetGrowthObligations_of_exactRemaining remaining

theorem finalTargetTorus_from_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_exactRemaining remaining hRange

theorem finalTargetMarkedTorus_from_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_exactRemaining remaining hRange

theorem finalTargetCayley_from_exactRemaining_closed
    (remaining : FinalExactRemainingTargetObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_exactRemaining remaining hRange

theorem finalOddHighModulusClosedInputs_holds_closed :
    FinalOddHighModulusClosedInputs :=
  finalOddHighModulusClosedInputs_holds

theorem finalOddHighModulusSuccessorInput_closed
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenSuccessorBridgeInput :=
  finalOddHighModulusSuccessorInput input

theorem finalOddHighModulusFiniteAnchorInput_closed
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenFiniteAnchorInput :=
  finalOddHighModulusFiniteAnchorInput input

theorem finalOddHighModulusProjectionKernelInput_closed
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenProjectionKernelInput :=
  finalOddHighModulusProjectionKernelInput input

theorem finalOddHighModulusGuideLocalityInput_closed
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenGuideLocalityInput :=
  finalOddHighModulusGuideLocalityInput input

theorem finalOddEndpointClosedInputs_holds_closed :
    FinalOddEndpointClosedInputs :=
  finalOddEndpointClosedInputs_holds

theorem finalOddEndpointInput_closed
    (input : FinalOddEndpointClosedInputs) :
    FinalEndpointInput :=
  finalOddEndpointInput input

theorem finalOddEndpointMarkedTransferAudit_closed
    (input : FinalOddEndpointClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit :=
  finalOddEndpointMarkedTransferAudit input

theorem finalPostPhaseGrowthArrows_of_promotions_closed
    (promotions : FinalPostPhaseGrowthPromotions) :
    FinalRemainingTargetPostPhaseGrowthArrows :=
  finalPostPhaseGrowthArrows_of_promotions promotions

theorem finalPostPhaseGrowthAssemblyInput_of_promotions_closed
    (promotions : FinalPostPhaseGrowthPromotions) :
    FinalTargetPostPhaseGrowthAssemblyInput :=
  finalPostPhaseGrowthAssemblyInput_of_promotions promotions

theorem finalExactRemainingTargetObligations_of_promotions_closed
    (remaining : FinalExactRemainingPromotionObligations) :
    FinalExactRemainingTargetObligations :=
  finalExactRemainingTargetObligations_of_promotions remaining

theorem finalTargetTorus_from_promotionObligations_closed
    (remaining : FinalExactRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_promotionObligations remaining hRange

theorem finalTargetMarkedTorus_from_promotionObligations_closed
    (remaining : FinalExactRemainingPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_promotionObligations remaining hRange

theorem finalTargetCayley_from_promotionObligations_closed
    (remaining : FinalExactRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_promotionObligations remaining hRange

theorem finalLowMarkedBasePromotions_of_individual_closed
    (d5m4 : FinalLowMarkedD5M4Promotion)
    (d7m4 : FinalLowMarkedD7M4Promotion)
    (d7m6 : FinalLowMarkedD7M6Promotion) :
    FinalLowMarkedBasePromotions :=
  finalLowMarkedBasePromotions_of_individual d5m4 d7m4 d7m6

theorem finalLowMarkedBasePromotions_of_sixRemaining_closed
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalLowMarkedBasePromotions :=
  finalLowMarkedBasePromotions_of_sixRemaining remaining

theorem finalPostPhaseGrowthPromotions_of_sixRemaining_closed
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalPostPhaseGrowthPromotions :=
  finalPostPhaseGrowthPromotions_of_sixRemaining remaining

theorem finalExactRemainingPromotionObligations_of_sixRemaining_closed
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalExactRemainingPromotionObligations :=
  finalExactRemainingPromotionObligations_of_sixRemaining remaining

theorem finalExactRemainingTargetObligations_of_sixRemaining_closed
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalExactRemainingTargetObligations :=
  finalExactRemainingTargetObligations_of_sixRemaining remaining

theorem finalTargetTorus_from_sixRemaining_closed
    (remaining : FinalSixRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_sixRemaining remaining hRange

theorem finalTargetMarkedTorus_from_sixRemaining_closed
    (remaining : FinalSixRemainingPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_sixRemaining remaining hRange

theorem finalTargetCayley_from_sixRemaining_closed
    (remaining : FinalSixRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_sixRemaining remaining hRange

theorem finalLowD5M4ClosedInputs_of_lowBase_closed
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalLowD5M4ClosedInputs :=
  finalLowD5M4ClosedInputs_of_lowBase input

theorem finalLowD5M4ClosedInputs_holds_closed :
    FinalLowD5M4ClosedInputs :=
  finalLowD5M4ClosedInputs_holds

theorem finalLowD5M4ResetTable_closed
    (input : FinalLowD5M4ClosedInputs) :
    D54ResetTableCertificate :=
  finalLowD5M4ResetTable input

theorem finalLowD5M4TerminalResetCycle_closed
    (input : FinalLowD5M4ClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  finalLowD5M4TerminalResetCycle input

theorem finalLowD5M4EndpointInput_closed
    (input : FinalLowD5M4ClosedInputs) :
    FinalEndpointInput :=
  finalLowD5M4EndpointInput input

theorem finalLowD5M4EndpointTransferInput_closed
    (input : FinalLowD5M4ClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput4 :=
  finalLowD5M4EndpointTransferInput input

theorem finalLowD7M4ClosedInputs_of_lowBase_closed
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalLowD7M4ClosedInputs :=
  finalLowD7M4ClosedInputs_of_lowBase input

theorem finalLowD7M4ClosedInputs_holds_closed :
    FinalLowD7M4ClosedInputs :=
  finalLowD7M4ClosedInputs_holds

theorem finalLowD7M4TerminalTraceCycle_closed
    (input : FinalLowD7M4ClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4) :=
  finalLowD7M4TerminalTraceCycle input

theorem finalLowD7M4EndpointInput_closed
    (input : FinalLowD7M4ClosedInputs) :
    FinalEndpointInput :=
  finalLowD7M4EndpointInput input

theorem finalLowD7M4EndpointTransferInput_closed
    (input : FinalLowD7M4ClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput4 :=
  finalLowD7M4EndpointTransferInput input

theorem finalLowD7M6ClosedInputs_of_lowBase_closed
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalLowD7M6ClosedInputs :=
  finalLowD7M6ClosedInputs_of_lowBase input

theorem finalLowD7M6ClosedInputs_holds_closed :
    FinalLowD7M6ClosedInputs :=
  finalLowD7M6ClosedInputs_holds

theorem finalLowD7M6TerminalTraceCycle_closed
    (input : FinalLowD7M6ClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6) :=
  finalLowD7M6TerminalTraceCycle input

theorem finalLowD7M6EndpointInput_closed
    (input : FinalLowD7M6ClosedInputs) :
    FinalEndpointInput :=
  finalLowD7M6EndpointInput input

theorem finalLowD7M6EndpointTransferInput_closed
    (input : FinalLowD7M6ClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput6 :=
  finalLowD7M6EndpointTransferInput input

theorem finalLowMarkedD5M4Promotion_of_targetPromotion_closed
    (promotion : FinalLowD5M4TargetPromotion) :
    FinalLowMarkedD5M4Promotion :=
  finalLowMarkedD5M4Promotion_of_targetPromotion promotion

theorem finalLowMarkedD7M4Promotion_of_targetPromotion_closed
    (promotion : FinalLowD7M4TargetPromotion) :
    FinalLowMarkedD7M4Promotion :=
  finalLowMarkedD7M4Promotion_of_targetPromotion promotion

theorem finalLowMarkedD7M6Promotion_of_targetPromotion_closed
    (promotion : FinalLowD7M6TargetPromotion) :
    FinalLowMarkedD7M6Promotion :=
  finalLowMarkedD7M6Promotion_of_targetPromotion promotion

theorem finalLowMarkedBasePromotions_of_refinedLow_closed
    (promotions : FinalRefinedLowBasePromotions) :
    FinalLowMarkedBasePromotions :=
  finalLowMarkedBasePromotions_of_refinedLow promotions

theorem finalSixRemainingPromotionObligations_of_refinedLow_closed
    (remaining : FinalSixRefinedLowPromotionObligations) :
    FinalSixRemainingPromotionObligations :=
  finalSixRemainingPromotionObligations_of_refinedLow remaining

theorem finalTargetTorus_from_refinedLow_closed
    (remaining : FinalSixRefinedLowPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedLow remaining hRange

theorem finalTargetMarkedTorus_from_refinedLow_closed
    (remaining : FinalSixRefinedLowPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedLow remaining hRange

theorem finalTargetCayley_from_refinedLow_closed
    (remaining : FinalSixRefinedLowPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedLow remaining hRange

theorem finalOddEndpointCertificateInputs_of_endpointInputs_closed
    (input : FinalOddEndpointClosedInputs) :
    FinalOddEndpointCertificateInputs :=
  finalOddEndpointCertificateInputs_of_endpointInputs input

theorem finalOddEndpointCertificateInputs_holds_closed :
    FinalOddEndpointCertificateInputs :=
  finalOddEndpointCertificateInputs_holds

theorem finalOddEndpointCertificateTerminalTrace4Cycle_closed
    (input : FinalOddEndpointCertificateInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4) :=
  finalOddEndpointCertificateTerminalTrace4Cycle input

theorem finalOddEndpointCertificateTerminalTrace6Cycle_closed
    (input : FinalOddEndpointCertificateInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6) :=
  finalOddEndpointCertificateTerminalTrace6Cycle input

theorem finalOddEndpointCertificateTerminalReset4Cycle_closed
    (input : FinalOddEndpointCertificateInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  finalOddEndpointCertificateTerminalReset4Cycle input

theorem finalOddEndpointCertificateMarkedTransferAudit_closed
    (input : FinalOddEndpointCertificateInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit :=
  finalOddEndpointCertificateMarkedTransferAudit input

theorem finalOddEndpointCertificateMarkedTransfer4_closed
    (input : FinalOddEndpointCertificateInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput4 :=
  finalOddEndpointCertificateMarkedTransfer4 input

theorem finalOddEndpointCertificateMarkedTransfer6_closed
    (input : FinalOddEndpointCertificateInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput6 :=
  finalOddEndpointCertificateMarkedTransfer6 input

theorem finalOddEndpointCertificatePhaseProductSupport_closed
    (input : FinalOddEndpointCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm :=
  finalOddEndpointCertificatePhaseProductSupport
    input parent h a m hh ha hm

theorem finalOddEndpointCertificatePhaseProductRealization_closed
    (input : FinalOddEndpointCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    PhaseDoublingProductRealizationInput parent h a m hh ha hm T
      reserveStep protectedStep reserveWord protectedWord n k :=
  finalOddEndpointCertificatePhaseProductRealization
    input parent h a m hh ha hm T reserveStep protectedStep
    hreserve hprotected reserveWord protectedWord n k

theorem finalOddEndpointCertificateCompletionCarry_closed
    (input : FinalOddEndpointCertificateInputs)
    {Base Coord : Type} [Finite Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base : Base) (C : CompletionCarryCertificate Base Coord m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hepsilon : IsUnit C.epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (completionCarry C.coordRead C.row C.tail)) :=
  finalOddEndpointCertificateCompletionCarry
    input baseStep rank base C hstep hepsilon

theorem finalOddEndpointCertificateB4FirstCompletion_closed
    (input : FinalOddEndpointCertificateInputs)
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (endpointB4FirstCompletionOnePointCertificate m).coordRead
          (cyclicCompletionRow
            (endpointB4FirstCompletionOnePointCertificate m).shift)
          (endpointB4FirstCompletionOnePointCertificate m).tail)) :=
  finalOddEndpointCertificateB4FirstCompletion input

theorem finalOddEndpointCertificateParentRange_closed
    (input : FinalOddEndpointCertificateInputs)
    {b m : Nat} (hb : 4 ≤ b)
    (hm : EvenModulusRange m) (hmle : m ≤ 2 * b + 1) :
    MarkedDimensionRange b m :=
  finalOddEndpointCertificateParentRange input hb hm hmle

theorem finalOddEndpointPromotion_of_targetPromotion_closed
    (promotion : FinalOddEndpointTargetPromotion) :
    FinalOddEndpointPromotion :=
  finalOddEndpointPromotion_of_targetPromotion promotion

theorem finalPostPhaseGrowthPromotions_of_refinedEndpoint_closed
    (promotions : FinalRefinedEndpointGrowthPromotions) :
    FinalPostPhaseGrowthPromotions :=
  finalPostPhaseGrowthPromotions_of_refinedEndpoint promotions

theorem finalSixRefinedLowPromotionObligations_of_refinedEndpoint_closed
    (remaining : FinalSixRefinedEndpointPromotionObligations) :
    FinalSixRefinedLowPromotionObligations :=
  finalSixRefinedLowPromotionObligations_of_refinedEndpoint remaining

theorem finalTargetTorus_from_refinedEndpoint_closed
    (remaining : FinalSixRefinedEndpointPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedEndpoint remaining hRange

theorem finalTargetMarkedTorus_from_refinedEndpoint_closed
    (remaining : FinalSixRefinedEndpointPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedEndpoint remaining hRange

theorem finalTargetCayley_from_refinedEndpoint_closed
    (remaining : FinalSixRefinedEndpointPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedEndpoint remaining hRange

theorem finalOddHighModulusCertificateInputs_of_highEvenInputs_closed
    (input : FinalOddHighModulusClosedInputs) :
    FinalOddHighModulusCertificateInputs :=
  finalOddHighModulusCertificateInputs_of_highEvenInputs input

theorem finalOddHighModulusCertificateInputs_holds_closed :
    FinalOddHighModulusCertificateInputs :=
  finalOddHighModulusCertificateInputs_holds

theorem finalOddHighModulusCertificateSuccessorInput_closed
    (input : FinalOddHighModulusCertificateInputs) :
    HighEvenSuccessorBridgeInput :=
  finalOddHighModulusCertificateSuccessorInput input

theorem finalOddHighModulusCertificateD5AnchorCheck_closed
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.d5HighEvenAnchorAuditBool = true :=
  finalOddHighModulusCertificateD5AnchorCheck input

theorem finalOddHighModulusCertificateD7AnchorCheck_closed
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.d7HighEvenAnchorAuditBool = true :=
  finalOddHighModulusCertificateD7AnchorCheck input

theorem finalOddHighModulusCertificateAnchorDimensionsNodup_closed
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.highEvenAnchorDimensions.Nodup :=
  finalOddHighModulusCertificateAnchorDimensionsNodup input

theorem finalOddHighModulusCertificateAnchorDimensionsCheck_closed
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.highEvenAnchorDimensionsAuditBool = true :=
  finalOddHighModulusCertificateAnchorDimensionsCheck input

theorem finalOddHighModulusCertificateV28FiniteInput_closed
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.v28FiniteInputCoforestAudit :=
  finalOddHighModulusCertificateV28FiniteInput input

theorem finalOddHighModulusCertificateV28FoldedTerminal_closed
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.v28FoldedTerminalInputAudit :=
  finalOddHighModulusCertificateV28FoldedTerminal input

theorem finalOddHighModulusCertificateD5CoforestRooted_closed
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d5CoforestRowsRootedAudit :=
  finalOddHighModulusCertificateD5CoforestRooted input

theorem finalOddHighModulusCertificateD5CoforestIncidence_closed
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d5CoforestRowsIncidenceAudit :=
  finalOddHighModulusCertificateD5CoforestIncidence input

theorem finalOddHighModulusCertificateD7CoforestRooted_closed
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d7Stage12CoforestRowsRootedAudit :=
  finalOddHighModulusCertificateD7CoforestRooted input

theorem finalOddHighModulusCertificateD7CoforestIncidence_closed
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d7Stage12CoforestRowsIncidenceAudit :=
  finalOddHighModulusCertificateD7CoforestIncidence input

theorem finalOddHighModulusCertificateProjectionKernelCoordinate_closed
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    lineSpan e x :=
  finalOddHighModulusCertificateProjectionKernelCoordinate
    input theta H e g x hThetaPlane hThetaTranslatedLine hxPlane
    hxTranslatedLine

theorem finalOddHighModulusCertificateProjectionKernelQuotientZero_closed
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    planeLineQuotientMk e g x hxPlane = planeLineQuotientZero e g :=
  finalOddHighModulusCertificateProjectionKernelQuotientZero
    input theta H e g x hThetaPlane hThetaTranslatedLine hxPlane
    hxTranslatedLine

theorem finalOddHighModulusCertificateTriangularKernelCoordinate_closed
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    lineSpan e1 x :=
  finalOddHighModulusCertificateTriangularKernelCoordinate
    input H e0 e1 g1 x hkill hxPlane hxTranslated

theorem finalOddHighModulusCertificateTriangularKernelQuotientZero_closed
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    planeLineQuotientMk e1 (triangularPlaneGenerator e0 g1)
      x hxPlane =
    planeLineQuotientZero e1 (triangularPlaneGenerator e0 g1) :=
  finalOddHighModulusCertificateTriangularKernelQuotientZero
    input H e0 e1 g1 x hkill hxPlane hxTranslated

theorem finalOddHighModulusCertificateOrdinaryNonzeroLocality_closed
    (input : FinalOddHighModulusCertificateInputs)
    {D : Nat} {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - ordinaryHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + ordinaryHighEvenRowDelta growthRow) ∧
      center row ∈ ordinaryHighEvenRowBoundary growthRow :=
  finalOddHighModulusCertificateOrdinaryNonzeroLocality
    input theta center rho growthRow hsubset hzero hne

theorem finalOddHighModulusCertificateOrdinaryBoundaryChoiceVanishes_closed
    (input : FinalOddHighModulusCertificateInputs)
    {D : Nat} {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate
      (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow)
      growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  finalOddHighModulusCertificateOrdinaryBoundaryChoiceVanishes
    input theta center hD growthRow C hzero row

theorem finalOddHighModulusCertificateOrdinaryOldGeneratorVanishes_closed
    (input : FinalOddHighModulusCertificateInputs)
    {D : Nat} {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (ordinaryHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  finalOddHighModulusCertificateOrdinaryOldGeneratorVanishes
    input theta center hD growthRow hzero row

theorem finalOddHighModulusCertificateChainedNonzeroLocality_closed
    (input : FinalOddHighModulusCertificateInputs)
    {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - chainedHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + chainedHighEvenRowDelta growthRow) ∧
      center row ∈ chainedHighEvenRowBoundary growthRow :=
  finalOddHighModulusCertificateChainedNonzeroLocality
    input theta center rho growthRow hsubset hzero hne

theorem finalOddHighModulusCertificateChainedBoundaryChoiceVanishes_closed
    (input : FinalOddHighModulusCertificateInputs)
    {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate
      (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
      growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  finalOddHighModulusCertificateChainedBoundaryChoiceVanishes
    input theta center growthRow C hzero row

theorem finalOddHighModulusCertificateChainedOldGeneratorVanishes_closed
    (input : FinalOddHighModulusCertificateInputs)
    {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (chainedHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  finalOddHighModulusCertificateChainedOldGeneratorVanishes
    input theta center growthRow hzero row

theorem finalOddHighModulusCertificateBranchCase_closed
    (input : FinalOddHighModulusCertificateInputs)
    {d m : Nat} (hodd : ∃ b : Nat, d = 2 * b + 1)
    (hmin : 5 ≤ d) (hm : EvenModulusRange m) :
    OddBranchRangeCase d m :=
  finalOddHighModulusCertificateBranchCase input hodd hmin hm

theorem finalOddHighModulusPromotion_of_targetPromotion_closed
    (promotion : FinalOddHighModulusTargetPromotion) :
    FinalOddHighModulusPromotion :=
  finalOddHighModulusPromotion_of_targetPromotion promotion

theorem finalRefinedEndpointGrowthPromotions_of_refinedHighEven_closed
    (promotions : FinalRefinedHighEvenGrowthPromotions) :
    FinalRefinedEndpointGrowthPromotions :=
  finalRefinedEndpointGrowthPromotions_of_refinedHighEven promotions

theorem finalPostPhaseGrowthPromotions_of_refinedHighEven_closed
    (promotions : FinalRefinedHighEvenGrowthPromotions) :
    FinalPostPhaseGrowthPromotions :=
  finalPostPhaseGrowthPromotions_of_refinedHighEven promotions

theorem finalSixRefinedEndpointPromotionObligations_of_refinedHighEven_closed
    (remaining : FinalSixRefinedHighEvenPromotionObligations) :
    FinalSixRefinedEndpointPromotionObligations :=
  finalSixRefinedEndpointPromotionObligations_of_refinedHighEven
    remaining

theorem finalTargetTorus_from_refinedHighEven_closed
    (remaining : FinalSixRefinedHighEvenPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedHighEven remaining hRange

theorem finalTargetMarkedTorus_from_refinedHighEven_closed
    (remaining : FinalSixRefinedHighEvenPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedHighEven remaining hRange

theorem finalTargetCayley_from_refinedHighEven_closed
    (remaining : FinalSixRefinedHighEvenPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedHighEven remaining hRange

theorem finalPhaseProductCertificateInputs_of_endpointCertificate_closed
    (input : FinalOddEndpointCertificateInputs) :
    FinalPhaseProductCertificateInputs :=
  finalPhaseProductCertificateInputs_of_endpointCertificate input

theorem finalPhaseProductCertificateInputs_holds_closed :
    FinalPhaseProductCertificateInputs :=
  finalPhaseProductCertificateInputs_holds

theorem finalPhaseProductCertificateSupport_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm :=
  finalPhaseProductCertificateSupport input parent h a m hh ha hm

theorem finalPhaseProductCertificateSupportSetEq_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  finalPhaseProductCertificateSupportSetEq input parent h a m hh ha hm

theorem finalPhaseProductCertificateSupportPointListLength_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).length =
      2 * a + 3 :=
  finalPhaseProductCertificateSupportPointListLength
    input parent h a m hh ha hm

theorem finalPhaseProductCertificateSupportPointListNodup_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).Nodup :=
  finalPhaseProductCertificateSupportPointListNodup
    input parent h a m hh ha hm

theorem finalPhaseProductCertificateSubsetReserveCylinder_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  finalPhaseProductCertificateSubsetReserveCylinder
    input parent h a m hh ha hm

theorem finalPhaseProductCertificateConstantParentProjection_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      parent :=
  finalPhaseProductCertificateConstantParentProjection
    input parent h a m hh ha hm

theorem finalPhaseProductCertificateConstantPhaseProjection_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      (2 : ZMod h) :=
  finalPhaseProductCertificateConstantPhaseProjection
    input parent h a m hh ha hm

theorem finalPhaseProductCertificateDisjointFromProtectedCylinder_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  finalPhaseProductCertificateDisjointFromProtectedCylinder
    input parent h a m hh ha hm T

theorem finalPhaseProductCertificateExistsUniqueSlot_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet) :
    ∃! i : Fin (2 * a + 3),
      (phaseProductReserveLineSlot parent h a m ha hm i).1 = x :=
  finalPhaseProductCertificateExistsUniqueSlot
    input parent h a m hh ha hm hx

theorem finalPhaseProductCertificatePointInjective_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) :=
  finalPhaseProductCertificatePointInjective
    input parent h a m hh ha hm

theorem finalPhaseProductCertificatePairInjective_closed
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) :=
  finalPhaseProductCertificatePairInjective
    input parent h a m hh ha hm

theorem finalPhaseProductCertificateRealization_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    PhaseDoublingProductRealizationInput parent h a m hh ha hm T
      reserveStep protectedStep reserveWord protectedWord n k :=
  finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord
    protectedWord n k

theorem finalPhaseProductCertificateRealizationSupport_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm :=
  finalPhaseProductCertificateRealizationSupport
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateProtectedWordFixesReserveSupport_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet) :
    wordEval protectedStep protectedWord x = x :=
  finalPhaseProductCertificateProtectedWordFixesReserveSupport
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k hx

theorem finalPhaseProductCertificateProtectedWordIterFixesReserveSupport_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet) :
    ((wordEval protectedStep protectedWord)^[k]) x = x :=
  finalPhaseProductCertificateProtectedWordIterFixesReserveSupport
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k hx

theorem finalPhaseProductCertificateProtectedWordMapsReserveSupport_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      (wordEval protectedStep protectedWord) :=
  finalPhaseProductCertificateProtectedWordMapsReserveSupport
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateProtectedWordIterMapsReserveSupport_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      ((wordEval protectedStep protectedWord)^[k]) :=
  finalPhaseProductCertificateProtectedWordIterMapsReserveSupport
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateReserveWordFixesProtectedCylinder_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval reserveStep reserveWord x = x :=
  finalPhaseProductCertificateReserveWordFixesProtectedCylinder
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k hx

theorem finalPhaseProductCertificateReserveWordIterFixesProtectedCylinder_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval reserveStep reserveWord)^[n]) x = x :=
  finalPhaseProductCertificateReserveWordIterFixesProtectedCylinder
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k hx

theorem finalPhaseProductCertificateReserveWordMapsProtectedCylinder_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval reserveStep reserveWord) :=
  finalPhaseProductCertificateReserveWordMapsProtectedCylinder
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateReserveWordIterMapsProtectedCylinder_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval reserveStep reserveWord)^[n]) :=
  finalPhaseProductCertificateReserveWordIterMapsProtectedCylinder
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateReserveWordCommutesProtectedWord_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      (wordEval reserveStep reserveWord) (wordEval protectedStep protectedWord) :=
  finalPhaseProductCertificateReserveWordCommutesProtectedWord
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateProtectedWordCommutesReserveWord_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      (wordEval protectedStep protectedWord) (wordEval reserveStep reserveWord) :=
  finalPhaseProductCertificateProtectedWordCommutesReserveWord
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateReserveWordIterCommutesProtectedWordIter_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      ((wordEval reserveStep reserveWord)^[n])
      ((wordEval protectedStep protectedWord)^[k]) :=
  finalPhaseProductCertificateReserveWordIterCommutesProtectedWordIter
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateProtectedWordIterCommutesReserveWordIter_closed
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      ((wordEval protectedStep protectedWord)^[k])
      ((wordEval reserveStep reserveWord)^[n]) :=
  finalPhaseProductCertificateProtectedWordIterCommutesReserveWordIter
    input parent h a m hh ha hm T reserveStep protectedStep hreserve
    hprotected reserveWord protectedWord n k

theorem finalOddEndpointPhaseProductCertificateInputs_of_endpointCertificate_closed
    (input : FinalOddEndpointCertificateInputs) :
    FinalOddEndpointPhaseProductCertificateInputs :=
  finalOddEndpointPhaseProductCertificateInputs_of_endpointCertificate
    input

theorem finalOddEndpointPhaseProductCertificateInputs_holds_closed :
    FinalOddEndpointPhaseProductCertificateInputs :=
  finalOddEndpointPhaseProductCertificateInputs_holds

theorem finalOddEndpointPhaseProductCertificatePhaseProductInput_closed
    (input : FinalOddEndpointPhaseProductCertificateInputs) :
    FinalPhaseProductCertificateInputs :=
  finalOddEndpointPhaseProductCertificatePhaseProductInput input

theorem finalOddEndpointCertificateInputs_of_phaseProductCertificate_closed
    (input : FinalOddEndpointPhaseProductCertificateInputs) :
    FinalOddEndpointCertificateInputs :=
  finalOddEndpointCertificateInputs_of_phaseProductCertificate input

theorem finalOddEndpointTargetPromotion_of_phaseProductPromotion_closed
    (promotion : FinalOddEndpointPhaseProductTargetPromotion) :
    FinalOddEndpointTargetPromotion :=
  finalOddEndpointTargetPromotion_of_phaseProductPromotion promotion

theorem finalRefinedHighEvenGrowthPromotions_of_phaseProduct_closed
    (promotions : FinalRefinedPhaseProductGrowthPromotions) :
    FinalRefinedHighEvenGrowthPromotions :=
  finalRefinedHighEvenGrowthPromotions_of_phaseProduct promotions

theorem finalSixRefinedHighEvenPromotionObligations_of_phaseProduct_closed
    (remaining : FinalSixRefinedPhaseProductPromotionObligations) :
    FinalSixRefinedHighEvenPromotionObligations :=
  finalSixRefinedHighEvenPromotionObligations_of_phaseProduct
    remaining

theorem finalTargetTorus_from_refinedPhaseProduct_closed
    (remaining : FinalSixRefinedPhaseProductPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedPhaseProduct remaining hRange

theorem finalTargetMarkedTorus_from_refinedPhaseProduct_closed
    (remaining : FinalSixRefinedPhaseProductPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedPhaseProduct remaining hRange

theorem finalTargetCayley_from_refinedPhaseProduct_closed
    (remaining : FinalSixRefinedPhaseProductPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedPhaseProduct remaining hRange

theorem finalTargetCertificateChecklistD3EvenPromotion_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalD3EvenBasePromotion :=
  finalTargetCertificateChecklistD3EvenPromotion checklist

theorem finalTargetCertificateChecklistD5M4Promotion_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalLowD5M4TargetPromotion :=
  finalTargetCertificateChecklistD5M4Promotion checklist

theorem finalTargetCertificateChecklistD7M4Promotion_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalLowD7M4TargetPromotion :=
  finalTargetCertificateChecklistD7M4Promotion checklist

theorem finalTargetCertificateChecklistD7M6Promotion_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalLowD7M6TargetPromotion :=
  finalTargetCertificateChecklistD7M6Promotion checklist

theorem finalTargetCertificateChecklistOddHighModulusPromotion_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalOddHighModulusTargetPromotion :=
  finalTargetCertificateChecklistOddHighModulusPromotion checklist

theorem finalTargetCertificateChecklistOddEndpointPromotion_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalOddEndpointPhaseProductTargetPromotion :=
  finalTargetCertificateChecklistOddEndpointPromotion checklist

theorem finalRefinedLowBasePromotions_of_certificateChecklist_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalRefinedLowBasePromotions :=
  finalRefinedLowBasePromotions_of_certificateChecklist checklist

theorem finalRefinedPhaseProductGrowthPromotions_of_certificateChecklist_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalRefinedPhaseProductGrowthPromotions :=
  finalRefinedPhaseProductGrowthPromotions_of_certificateChecklist
    checklist

theorem finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalSixRefinedPhaseProductPromotionObligations :=
  finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist
    checklist

theorem finalTargetTorus_from_certificateChecklist_closed
    (checklist : FinalTargetCertificateChecklist)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_certificateChecklist checklist hRange

theorem finalTargetMarkedTorus_from_certificateChecklist_closed
    (checklist : FinalTargetCertificateChecklist)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_certificateChecklist checklist hRange

theorem finalTargetCayley_from_certificateChecklist_closed
    (checklist : FinalTargetCertificateChecklist)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_certificateChecklist checklist hRange

theorem finalTargetCertificateInputInventory_holds_closed :
    FinalTargetCertificateInputInventory :=
  finalTargetCertificateInputInventory_holds

theorem finalTargetCertificateInventoryD3EvenInput_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalD3EvenBaseClosedInputs :=
  finalTargetCertificateInventoryD3EvenInput inventory

theorem finalTargetCertificateInventoryD5M4Input_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalLowD5M4ClosedInputs :=
  finalTargetCertificateInventoryD5M4Input inventory

theorem finalTargetCertificateInventoryD7M4Input_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalLowD7M4ClosedInputs :=
  finalTargetCertificateInventoryD7M4Input inventory

theorem finalTargetCertificateInventoryD7M6Input_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalLowD7M6ClosedInputs :=
  finalTargetCertificateInventoryD7M6Input inventory

theorem finalTargetCertificateInventoryOddHighModulusInput_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalOddHighModulusCertificateInputs :=
  finalTargetCertificateInventoryOddHighModulusInput inventory

theorem finalTargetCertificateInventoryPhaseProductInput_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalPhaseProductCertificateInputs :=
  finalTargetCertificateInventoryPhaseProductInput inventory

theorem finalTargetCertificateInventoryOddEndpointInput_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalOddEndpointPhaseProductCertificateInputs :=
  finalTargetCertificateInventoryOddEndpointInput inventory

theorem finalTargetCertificateInventoryEndpointPhaseProductInput_closed
    (inventory : FinalTargetCertificateInputInventory) :
    FinalPhaseProductCertificateInputs :=
  finalTargetCertificateInventoryEndpointPhaseProductInput inventory

theorem finalTargetCertificateReadyPackage_of_checklist_closed
    (checklist : FinalTargetCertificateChecklist) :
    FinalTargetCertificateReadyPackage :=
  finalTargetCertificateReadyPackage_of_checklist checklist

theorem finalTargetCertificateReadyPackageInventory_closed
    (ready : FinalTargetCertificateReadyPackage) :
    FinalTargetCertificateInputInventory :=
  finalTargetCertificateReadyPackageInventory ready

theorem finalTargetCertificateReadyPackageChecklist_closed
    (ready : FinalTargetCertificateReadyPackage) :
    FinalTargetCertificateChecklist :=
  finalTargetCertificateReadyPackageChecklist ready

theorem finalTargetReadyPackageD3EvenTarget_closed
    (ready : FinalTargetCertificateReadyPackage)
    {m : Nat} (hm : EvenModulusRange m) :
    FinalOrdinaryTarget 3 m :=
  finalTargetReadyPackageD3EvenTarget ready hm

theorem finalTargetReadyPackageD5M4Target_closed
    (ready : FinalTargetCertificateReadyPackage) :
    FinalMarkedTarget 5 4 :=
  finalTargetReadyPackageD5M4Target ready

theorem finalTargetReadyPackageD7M4Target_closed
    (ready : FinalTargetCertificateReadyPackage) :
    FinalMarkedTarget 7 4 :=
  finalTargetReadyPackageD7M4Target ready

theorem finalTargetReadyPackageD7M6Target_closed
    (ready : FinalTargetCertificateReadyPackage) :
    FinalMarkedTarget 7 6 :=
  finalTargetReadyPackageD7M6Target ready

theorem finalTargetReadyPackageOddHighModulusTarget_closed
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hd : 5 ≤ d) (hodd : ∃ b : Nat, d = 2 * b + 1)
    (hm : EvenModulusRange m) (hdm : d < m) :
    FinalMarkedTarget d m :=
  finalTargetReadyPackageOddHighModulusTarget ready hd hodd hm hdm

theorem finalTargetReadyPackageOddEndpointTarget_closed
    (ready : FinalTargetCertificateReadyPackage)
    {b m : Nat} (hb : 4 ≤ b) (hRange : MarkedDimensionRange b m)
    (parent : FinalMarkedTarget b m) :
    FinalMarkedTarget (2 * b + 1) m :=
  finalTargetReadyPackageOddEndpointTarget ready hb hRange parent

theorem finalSixRefinedPhaseProductPromotionObligations_of_readyPackage_closed
    (ready : FinalTargetCertificateReadyPackage) :
    FinalSixRefinedPhaseProductPromotionObligations :=
  finalSixRefinedPhaseProductPromotionObligations_of_readyPackage ready

theorem finalTargetTorus_from_readyPackage_closed
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_readyPackage ready hRange

theorem finalTargetMarkedTorus_from_readyPackage_closed
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_readyPackage ready hRange

theorem finalTargetCayley_from_readyPackage_closed
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_readyPackage ready hRange

theorem finalRootFlatTorusModelEdgePartition_closed
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    Shared.IsCayleyEdgePartition
      (finalRootFlatModelColorDir schedule torusEquiv) :=
  finalRootFlatTorusModelEdgePartition model

theorem finalRootFlatTorusModelColorHamiltonian_closed
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    Shared.IsCayleyColorHamiltonian
      (finalRootFlatModelColorDir schedule torusEquiv) :=
  finalRootFlatTorusModelColorHamiltonian model

theorem finalRootFlatTorusModelCayley_closed
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalRootFlatTorusModelCayley model

theorem finalRootFlatOrdinaryTarget_of_model_closed
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    FinalOrdinaryTarget d m :=
  finalRootFlatOrdinaryTarget_of_model model

theorem finalRootFlatMarkedTarget_of_model_closed
    {d m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor d)
        (Shared.TorusDirection d) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex d m}
    (model :
      FinalRootFlatTorusModel d m RootState schedule torusEquiv) :
    FinalMarkedTarget d m :=
  finalRootFlatMarkedTarget_of_model model

theorem finalRootFlatCayley_of_certificate_closed
    {d m : Nat} (certificate : FinalRootFlatTorusCertificate d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalRootFlatCayley_of_certificate certificate

theorem finalRootFlatOrdinaryTarget_of_certificate_closed
    {d m : Nat} (certificate : FinalRootFlatTorusCertificate d m) :
    FinalOrdinaryTarget d m :=
  finalRootFlatOrdinaryTarget_of_certificate certificate

theorem finalRootFlatMarkedTarget_of_certificate_closed
    {d m : Nat} (certificate : FinalRootFlatTorusCertificate d m) :
    FinalMarkedTarget d m :=
  finalRootFlatMarkedTarget_of_certificate certificate

theorem finalD3EvenRootFlatModelEdgePartition_closed
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    Shared.IsCayleyEdgePartition
      (finalD3RootFlatModelColorDir schedule torusEquiv) :=
  finalD3EvenRootFlatModelEdgePartition model

theorem finalD3EvenRootFlatModelColorHamiltonian_closed
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    Shared.IsCayleyColorHamiltonian
      (finalD3RootFlatModelColorDir schedule torusEquiv) :=
  finalD3EvenRootFlatModelColorHamiltonian model

theorem finalD3EvenRootFlatModelCayley_closed
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    Shared.CayleyHamiltonDecomposition 3 m :=
  finalD3EvenRootFlatModelCayley model

theorem finalD3EvenTarget_of_rootFlatModel_closed
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    FinalOrdinaryTarget 3 m :=
  finalD3EvenTarget_of_rootFlatModel model

theorem finalD3EvenTarget_of_rootFlatCertificate_closed
    {m : Nat} (certificate : FinalD3EvenRootFlatCertificate m) :
    FinalOrdinaryTarget 3 m :=
  finalD3EvenTarget_of_rootFlatCertificate certificate

theorem finalD3EvenTarget_of_rootFlatCertificateFamily_closed
    (family : FinalD3EvenRootFlatCertificateFamily)
    {m : Nat} (hm : EvenModulusRange m) :
    FinalOrdinaryTarget 3 m :=
  finalD3EvenTarget_of_rootFlatCertificateFamily family hm

theorem finalD3EvenBasePromotion_of_rootFlatCertificateFamily_closed
    (family : FinalD3EvenRootFlatCertificateFamily) :
    FinalD3EvenBasePromotion :=
  finalD3EvenBasePromotion_of_rootFlatCertificateFamily family

theorem finalTargetCertificateChecklist_of_d3RootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat) :
    FinalTargetCertificateChecklist :=
  finalTargetCertificateChecklist_of_d3RootFlatChecklist checklist

theorem finalTargetReadyPackage_of_d3RootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat) :
    FinalTargetCertificateReadyPackage :=
  finalTargetReadyPackage_of_d3RootFlatChecklist checklist

theorem finalTargetTorus_from_d3RootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_d3RootFlatChecklist checklist hRange

theorem finalTargetMarkedTorus_from_d3RootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_d3RootFlatChecklist checklist hRange

theorem finalTargetCayley_from_d3RootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_d3RootFlatChecklist checklist hRange

theorem finalLowD5M4Target_of_rootFlatCertificateFamily_closed
    (family : FinalLowD5M4RootFlatCertificateFamily)
    (input : FinalLowD5M4ClosedInputs) :
    FinalMarkedTarget 5 4 :=
  finalLowD5M4Target_of_rootFlatCertificateFamily family input

theorem finalLowD7M4Target_of_rootFlatCertificateFamily_closed
    (family : FinalLowD7M4RootFlatCertificateFamily)
    (input : FinalLowD7M4ClosedInputs) :
    FinalMarkedTarget 7 4 :=
  finalLowD7M4Target_of_rootFlatCertificateFamily family input

theorem finalLowD7M6Target_of_rootFlatCertificateFamily_closed
    (family : FinalLowD7M6RootFlatCertificateFamily)
    (input : FinalLowD7M6ClosedInputs) :
    FinalMarkedTarget 7 6 :=
  finalLowD7M6Target_of_rootFlatCertificateFamily family input

theorem finalLowD5M4TargetPromotion_of_rootFlatCertificateFamily_closed
    (family : FinalLowD5M4RootFlatCertificateFamily) :
    FinalLowD5M4TargetPromotion :=
  finalLowD5M4TargetPromotion_of_rootFlatCertificateFamily family

theorem finalLowD7M4TargetPromotion_of_rootFlatCertificateFamily_closed
    (family : FinalLowD7M4RootFlatCertificateFamily) :
    FinalLowD7M4TargetPromotion :=
  finalLowD7M4TargetPromotion_of_rootFlatCertificateFamily family

theorem finalLowD7M6TargetPromotion_of_rootFlatCertificateFamily_closed
    (family : FinalLowD7M6RootFlatCertificateFamily) :
    FinalLowD7M6TargetPromotion :=
  finalLowD7M6TargetPromotion_of_rootFlatCertificateFamily family

theorem finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies_closed
    (families : FinalLowBaseRootFlatCertificateFamilies) :
    FinalRefinedLowBasePromotions :=
  finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
    families

theorem finalLowBaseRootFlatD5M4Target_closed
    (families : FinalLowBaseRootFlatCertificateFamilies)
    (input : FinalLowD5M4ClosedInputs) :
    FinalMarkedTarget 5 4 :=
  finalLowBaseRootFlatD5M4Target families input

theorem finalLowBaseRootFlatD7M4Target_closed
    (families : FinalLowBaseRootFlatCertificateFamilies)
    (input : FinalLowD7M4ClosedInputs) :
    FinalMarkedTarget 7 4 :=
  finalLowBaseRootFlatD7M4Target families input

theorem finalLowBaseRootFlatD7M6Target_closed
    (families : FinalLowBaseRootFlatCertificateFamilies)
    (input : FinalLowD7M6ClosedInputs) :
    FinalMarkedTarget 7 6 :=
  finalLowBaseRootFlatD7M6Target families input

theorem finalTargetCertificateChecklistWithD3RootFlat_of_lowRootFlat_closed
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat) :
    FinalTargetCertificateChecklistWithD3RootFlat :=
  finalTargetCertificateChecklistWithD3RootFlat_of_lowRootFlat
    checklist

theorem finalTargetCertificateChecklist_of_d3AndLowRootFlat_closed
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat) :
    FinalTargetCertificateChecklist :=
  finalTargetCertificateChecklist_of_d3AndLowRootFlat checklist

theorem finalTargetReadyPackage_of_d3AndLowRootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat) :
    FinalTargetCertificateReadyPackage :=
  finalTargetReadyPackage_of_d3AndLowRootFlatChecklist checklist

theorem finalTargetTorus_from_d3AndLowRootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_d3AndLowRootFlatChecklist checklist hRange

theorem finalTargetMarkedTorus_from_d3AndLowRootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_d3AndLowRootFlatChecklist checklist hRange

theorem finalTargetCayley_from_d3AndLowRootFlatChecklist_closed
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_d3AndLowRootFlatChecklist checklist hRange

end EvenV11
