import RoundComposite.SeedSemigroup

namespace RoundComposite
namespace Concrete

def OddCoreHighGE13 (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m : Nat}, 13 ≤ d → Odd d → 3 ≤ m → Odd m → d ≤ m →
    Solved d m

def OddCoreHighModulusPrefixCount (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m : Nat}, Odd d → 5 ≤ d → 3 ≤ m → Odd m → d ≤ m →
    Solved d m

def OddCoreSmallGE13 (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m : Nat}, 13 ≤ d → Odd d → 3 ≤ m → Odd m → m < d →
    Solved d m

def D11SmallModulusLiftFromD5Base (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {m : Nat}, 3 ≤ m → Odd m → m < 11 →
    Solved 5 m →
    Solved 11 m

def OddCoreSmallModulusLiftOfBase (Solved : Nat → Nat → Prop) : Prop :=
  ∀ {d m b : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    Solved b m →
    2 * b < d ∧ d ≤ 3 * b →
    Solved d m

def OddCoreHighModulusPrefixCountGoal : Prop :=
  ∀ {d m : Nat}, Odd d → 5 ≤ d → Odd m → d ≤ m →
    StandardCayleySolved d m

def PrefixCountLayerRealizationGoal : Prop :=
  ∀ {d m : Nat} (hd2 : 2 ≤ d) (C : PrefixCount.Parts d),
    C.Admissible m →
    Nonempty (PrefixCount.LayerPermCounts d m (C.toMatrix hd2))

def PrefixCountGeometricCriterionGoal : Prop :=
  ∀ {d m : Nat} (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    StandardCayleySolved d m

abbrev PrefixCountRootState (d m : Nat) :=
  Fin (d - 1) → ZMod m

def prefixCountRootLayerEquivSucc (n m : Nat) :
    ZMod m × (Fin n → ZMod m) ≃ Shared.TorusVertex (n + 1) m where
  toFun tw := Fin.snoc tw.2 (tw.1 - ∑ j : Fin n, tw.2 j)
  invFun x := (∑ i : Fin (n + 1), x i, fun j : Fin n => x j.castSucc)
  left_inv := by
    intro tw
    ext
    · simp [Fin.sum_snoc]
    · simp
  right_inv := by
    intro x
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · simp only [Fin.snoc_last]
      rw [Fin.sum_univ_castSucc]
      abel

def prefixCountRootStepSucc {n m : Nat}
    (i : Fin (n + 1)) (w : Fin n → ZMod m) : Fin n → ZMod m :=
  fun j => if i = j.castSucc then w j + 1 else w j

theorem prefixCountRootStepSucc_sum_castSucc {n m : Nat}
    (i : Fin n) (w : Fin n → ZMod m) :
    (∑ j : Fin n, prefixCountRootStepSucc i.castSucc w j)
      = (∑ j : Fin n, w j) + 1 := by
  classical
  calc
    (∑ j : Fin n, prefixCountRootStepSucc i.castSucc w j)
        = ∑ j : Fin n, (w j + if i = j then (1 : ZMod m) else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases h : i = j
            · subst j
              simp [prefixCountRootStepSucc]
            · have hcast : i.castSucc ≠ j.castSucc := by
                intro hc
                exact h (Fin.castSucc_injective n hc)
              simp [prefixCountRootStepSucc, h, hcast]
    _ = (∑ j : Fin n, w j) + ∑ j : Fin n, (if i = j then (1 : ZMod m) else 0) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin n, w j) + 1 := by
            simp

theorem prefixCountRootStepSucc_sum_last {n m : Nat}
    (w : Fin n → ZMod m) :
    (∑ j : Fin n, prefixCountRootStepSucc (Fin.last n) w j)
      = ∑ j : Fin n, w j := by
  classical
  have hlast : ∀ j : Fin n, (Fin.last n : Fin (n + 1)) ≠ j.castSucc := by
    intro j h
    exact Fin.castSucc_ne_last j h.symm
  simp [prefixCountRootStepSucc, hlast]

theorem prefixCountRootLayerEquivSucc_step {n m : Nat}
    (i : Fin (n + 1)) (tw : ZMod m × (Fin n → ZMod m)) :
    prefixCountRootLayerEquivSucc n m
        (tw.1 + 1, prefixCountRootStepSucc i tw.2)
      =
      prefixCountRootLayerEquivSucc n m tw + Shared.torusBasis (n + 1) m i := by
  classical
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · simp only [prefixCountRootLayerEquivSucc, Equiv.coe_fn_mk,
      Fin.snoc_castSucc, Pi.add_apply, Shared.torusBasis]
    by_cases h : i = j.castSucc
    · rw [prefixCountRootStepSucc, if_pos h, if_pos h.symm]
    · have h' : j.castSucc ≠ i := h ∘ Eq.symm
      rw [prefixCountRootStepSucc, if_neg h, if_neg h']
      simp
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [prefixCountRootLayerEquivSucc, Equiv.coe_fn_mk,
        Fin.snoc_last, Pi.add_apply, Shared.torusBasis]
      have hlast : (Fin.last n : Fin (n + 1)) ≠ j.castSucc :=
        (Fin.castSucc_ne_last j).symm
      simp [prefixCountRootStepSucc_sum_castSucc, hlast]
    · simp only [prefixCountRootLayerEquivSucc, Equiv.coe_fn_mk,
        Fin.snoc_last, Pi.add_apply, Shared.torusBasis]
      rw [prefixCountRootStepSucc_sum_last]
      simp
      ring_nf

def prefixCountRootLayerEquiv (d m : Nat) (hd1 : 1 ≤ d) :
    ZMod m × PrefixCountRootState d m ≃ Shared.TorusVertex d m :=
  (prefixCountRootLayerEquivSucc (d - 1) m).trans
    (Equiv.arrowCongr (finCongr (Nat.sub_add_cancel hd1)) (Equiv.refl _))

def prefixCountRootStep (d m : Nat) :
    Fin d → PrefixCountRootState d m → PrefixCountRootState d m :=
  fun i w j => if (i : Nat) = j then w j + 1 else w j

theorem prefixCountRootStep_eq_succ_cast {d m : Nat} (hd1 : 1 ≤ d)
    (i : Fin d) (w : PrefixCountRootState d m) :
    prefixCountRootStep d m i w =
      prefixCountRootStepSucc
        ((finCongr (Nat.sub_add_cancel hd1)).symm i) w := by
  funext j
  rw [prefixCountRootStep, prefixCountRootStepSucc]
  by_cases hcast :
      (finCongr (Nat.sub_add_cancel hd1)).symm i = j.castSucc
  · have hval : (i : Nat) = j := by
      have := congrArg Fin.val hcast
      simpa using this
    have hcast' :
        Fin.cast (Nat.sub_add_cancel hd1).symm i = j.castSucc := by
      simpa using hcast
    simp [hcast', hval]
  · have hval : ¬ (i : Nat) = j := by
      intro hv
      apply hcast
      ext
      simp [hv]
    have hcast' :
        ¬ Fin.cast (Nat.sub_add_cancel hd1).symm i = j.castSucc := by
      intro h
      exact hcast (by simpa using h)
    simp [hcast', hval]

theorem prefixCountRootStepSucc_bijective {n m : Nat}
    (i : Fin (n + 1)) :
    Function.Bijective (prefixCountRootStepSucc (m := m) i) := by
  constructor
  · intro w v h
    funext j
    have hj := congrFun h j
    by_cases hij : i = j.castSucc
    · have hj' := congrArg (fun x : ZMod m => x - 1) hj
      simpa [prefixCountRootStepSucc, hij, sub_eq_add_neg, add_assoc] using hj'
    · simpa [prefixCountRootStepSucc, hij] using hj
  · intro v
    refine ⟨fun j => if i = j.castSucc then v j - 1 else v j, ?_⟩
    funext j
    by_cases hij : i = j.castSucc
    · simp [prefixCountRootStepSucc, hij, sub_eq_add_neg, add_assoc]
    · simp [prefixCountRootStepSucc, hij]

theorem prefixCountRootStep_bijective {d m : Nat}
    (i : Fin d) :
    Function.Bijective (prefixCountRootStep d m i) := by
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hd1 : 1 ≤ d := Nat.succ_le_iff.mpr hdpos
  let e := (finCongr (Nat.sub_add_cancel hd1)).symm i
  have hfun : prefixCountRootStep d m i = prefixCountRootStepSucc e := by
    funext w
    exact prefixCountRootStep_eq_succ_cast hd1 i w
  simpa [hfun] using prefixCountRootStepSucc_bijective (m := m) e

theorem prefixCountRootLayerEquiv_step {d m : Nat} (hd1 : 1 ≤ d)
    (i : Fin d) (tw : ZMod m × PrefixCountRootState d m) :
    prefixCountRootLayerEquiv d m hd1
        (tw.1 + 1, prefixCountRootStep d m i tw.2)
      =
      prefixCountRootLayerEquiv d m hd1 tw + Shared.torusBasis d m i := by
  rw [prefixCountRootStep_eq_succ_cast hd1 i tw.2]
  unfold prefixCountRootLayerEquiv
  simp only [Equiv.trans_apply]
  rw [prefixCountRootLayerEquivSucc_step]
  funext k
  simp [Equiv.arrowCongr, Shared.torusBasis]

def PrefixCountRootFlatReturnGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    Shared.RootFlatReturnCriterion
      (Fin d) (Fin d) (PrefixCountRootState d m) m

def PrefixCountRootFlatCanonicalReturnGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    ∃ cert : Shared.RootFlatCertificate
      (Fin d) (Fin d) (PrefixCountRootState d m) m,
      cert.schedule.step = prefixCountRootStep d m

def PrefixCountRootFlatCanonicalScheduleCriterionGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    ∃ S : Shared.RootFlatSchedule
        (Fin d) (Fin d) (PrefixCountRootState d m) m,
      S.step = prefixCountRootStep d m ∧
      S.rowLatin ∧ S.layerBijective ∧ S.returnsSingleCycle

theorem prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal) :
    PrefixCountRootFlatCanonicalReturnGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L
  rcases hSchedule hd2 hdodd hd5 hmodd hdm hC L with
    ⟨S, hStep, hRow, hLayer, hReturn⟩
  exact ⟨{
    schedule := S
    rowLatin := hRow
    layerBijective := hLayer
    returnsSingleCycle := hReturn
  }, hStep⟩

theorem prefixCountRootFlatCanonicalScheduleCriterionGoal_of_return
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    PrefixCountRootFlatCanonicalScheduleCriterionGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L
  rcases hReturn hd2 hdodd hd5 hmodd hdm hC L with ⟨cert, hStep⟩
  exact ⟨cert.schedule, hStep, cert.rowLatin, cert.layerBijective,
    cert.returnsSingleCycle⟩

theorem prefixCountRootFlatCanonicalReturnGoal_iff_scheduleCriterion :
    PrefixCountRootFlatCanonicalReturnGoal ↔
      PrefixCountRootFlatCanonicalScheduleCriterionGoal :=
  ⟨prefixCountRootFlatCanonicalScheduleCriterionGoal_of_return,
    prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion⟩

def PrefixCountRootFlatCayleyLiftGoal : Prop :=
  ∀ {d m : Nat} [NeZero m],
    2 ≤ d → Odd d → 5 ≤ d → Odd m → d ≤ m →
    Shared.RootFlatLayeredHamiltonDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m →
    StandardCayleySolved d m

def RootFlatCayleyStepCompatible {d m : Nat} [NeZero m] {RootState : Type*}
    (D : Shared.RootFlatLayeredDecomposition (Fin d) (Fin d) RootState m)
    (E : ZMod m × RootState ≃ Shared.TorusVertex d m) : Prop :=
  ∀ c : Fin d, ∀ tw : ZMod m × RootState,
    E (D.schedule.fullStep c tw) =
      Shared.cayleyColorStep
        (fun c x => D.schedule.dir (E.symm x).1 (E.symm x).2 c)
        c (E tw)

def PrefixCountRootFlatEquivLiftGoal : Prop :=
  ∀ {d m : Nat} [NeZero m],
    2 ≤ d → Odd d → 5 ≤ d → Odd m → d ≤ m →
    (D : Shared.RootFlatLayeredDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m) →
    ∃ E : ZMod m × PrefixCountRootState d m ≃ Shared.TorusVertex d m,
      RootFlatCayleyStepCompatible D E

def D11SmallModulusFromD5BaseGoal : Prop :=
  ∀ {m : Nat}, 3 ≤ m → Odd m → m < 11 →
    StandardCayleySolved 5 m →
    StandardCayleySolved 11 m

def OddCoreSmallModulusOfBaseGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    2 * b < d ∧ d ≤ 3 * b →
    StandardCayleySolved d m

def OddCoreSmallModulusOfUnitPacketsGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    StandardCayleySolved d m

def OddCoreSmallModulusUnitPacketLiftGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 11 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    StandardCayleySolved d m

def OddCoreSmallModulusSlackPacketLiftGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 11 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    d - b > b →
    m ^ b > m * d * (d - b) →
    StandardCayleySolved d m

def OddCoreSmallModulusSlackPacketLiftAddGoal : Prop :=
  ∀ {d m b T : Nat},
    Odd d → 11 ≤ d →
    Odd m → 3 ≤ m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    d = b + T →
    T > b →
    m ^ b > m * d * T →
    StandardCayleySolved d m

theorem oddCoreSmallModulusSlackPacketLiftAddGoal_of_slackPacketLift
    (hLift : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddCoreSmallModulusSlackPacketLiftAddGoal := by
  intro d m b T hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hdEq hT hSlack
  have hTail : d - b > b := by omega
  have hSlack' : m ^ b > m * d * (d - b) := by
    have hTsub : T = d - b := by omega
    simpa [hTsub] using hSlack
  exact hLift hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hTail hSlack'

theorem oddCoreSmallModulusSlackPacketLiftGoal_of_add
    (hLift : OddCoreSmallModulusSlackPacketLiftAddGoal) :
    OddCoreSmallModulusSlackPacketLiftGoal := by
  intro d m b hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hTail hSlack
  have hdEq : d = b + (d - b) := by omega
  exact hLift hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hdEq hTail hSlack

theorem oddCoreSmallModulusSlackPacketLiftGoal_iff_add :
    OddCoreSmallModulusSlackPacketLiftGoal ↔
      OddCoreSmallModulusSlackPacketLiftAddGoal :=
  ⟨oddCoreSmallModulusSlackPacketLiftAddGoal_of_slackPacketLift,
    oddCoreSmallModulusSlackPacketLiftGoal_of_add⟩

def OddSuccessorSmallModulusSlackPacketLiftAddGoal : Prop :=
  ∀ {b m T : Nat},
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    StandardCayleySolved (b + T) m

theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_coreAdd
    (hLift : OddCoreSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal := by
  intro b m T hb5 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits hT hSlack
  have hdodd : Odd (b + T) := by
    rw [hT]
    exact ⟨b, by omega⟩
  have hd11 : 11 ≤ b + T := by omega
  have hTgt : T > b := by omega
  exact hLift
    (d := b + T) (m := m) (b := b) (T := T)
    hdodd hd11 hmodd hm3 hmd hbSolved packets
    hlen hsum hpacketSum hpacketUnits rfl hTgt hSlack

def OddSuccessorSmallModulusBaseTailGoal : Prop :=
  ∀ {b m : Nat},
    5 ≤ b →
    Odd m → 3 ≤ m →
    m < 2 * b + 1 →
    StandardCayleySolved b m →
    StandardCayleySolved (2 * b + 1) m

def OddCoreSmallBaseSlackWitnessGoal : Prop :=
  ∀ {d m : Nat},
    Odd d → 13 ≤ d →
    Odd m → 3 ≤ m → m < d →
    ∃ w : SmallBaseUnitPacketWitness d m,
      d - w.b > w.b ∧
      m ^ w.b > m * d * (d - w.b)

theorem oddCoreSmallBaseSlackWitnessGoal_of_seed_semigroup :
    OddCoreSmallBaseSlackWitnessGoal := by
  intro d m hdodd hd13 hmodd hm3 hmd
  rcases seed_semigroup_base_available_with_hall_slack
      hdodd hd13 hm3 hmd with
    ⟨b, hbSeed, hbLow, hbHigh, hTail, hSlack⟩
  have hbRange : 2 * b < d ∧ d ≤ 3 * b := ⟨hbLow, hbHigh⟩
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec hm3 hmodd hbRange
  refine ⟨{
    b := b
    seed := hbSeed
    range := hbRange
    packets := _root_.RoundComposite.unitCarryPackets m b d
    packets_length := hpackets.1
    packets_total_length := hpackets.2.1
    packet_sum := fun packet hp => (hpackets.2.2 packet hp).1
    packet_units := fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha
  }, hTail, hSlack⟩

theorem oddCoreHighModulusPrefixCount_of_goal
    (hHigh : OddCoreHighModulusPrefixCountGoal) :
    OddCoreHighModulusPrefixCount StandardCayleySolved := by
  intro d m hdodd hd5 _hm3 hmodd hdm
  exact hHigh hdodd hd5 hmodd hdm

theorem oddSuccessorClosureGoal_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal := by
  intro b m hb5 hmodd hm3 hbSolved
  by_cases hmd : 2 * b + 1 ≤ m
  · exact hHigh ⟨b, rfl⟩ (by omega) hmodd hmd
  · exact hSmall hb5 hmodd hm3 (lt_of_not_ge hmd) hbSolved

theorem odd_successor_closure_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_high_and_successorSmall hHigh hSmall)
    hb5 hmodd hm3 hb

theorem oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddSuccessorSmallModulusBaseTailGoal := by
  intro b m hb5 hmodd hm3 hmSmall hbSolved
  have hdodd : Odd (2 * b + 1) := ⟨b, rfl⟩
  have hd11 : 11 ≤ 2 * b + 1 := by omega
  have hRange : 2 * b < 2 * b + 1 ∧ 2 * b + 1 ≤ 3 * b := by omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := b) (d := 2 * b + 1) (m := m) hm3 hmodd hRange
  exact hSmallPacket
    (d := 2 * b + 1) (b := b)
    hdodd hd11 hmodd hm3 hmSmall hbSolved
    (_root_.RoundComposite.unitCarryPackets m b (2 * b + 1))
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)
    (by omega)
    (_root_.RoundComposite.successor_hall_slack hb5 hm3)

theorem odd_successor_small_modulus_base_tail_of_slackPacketLift
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift hSmallPacket)
    hb5 hmodd hm3 hmSmall hb

theorem oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorSmallModulusBaseTailGoal := by
  intro b m hb5 hmodd hm3 hmSmall hbSolved
  have hRange :
      2 * b < b + (b + 1) ∧ b + (b + 1) ≤ 3 * b := by
    omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := b) (d := b + (b + 1)) (m := m) hm3 hmodd hRange
  have hmSmall' : m < b + (b + 1) := by omega
  have hSlack : m ^ b > m * (b + (b + 1)) * (b + 1) := by
    have h0 := _root_.RoundComposite.successor_hall_slack hb5 hm3
    have hsum : b + (b + 1) = 2 * b + 1 := by omega
    have htail : (2 * b + 1) - b = b + 1 := by omega
    simpa [hsum, htail] using h0
  have hSolved : StandardCayleySolved (b + (b + 1)) m :=
    hSmallPacket
      (b := b) (m := m) (T := b + 1)
      hb5 hmodd hm3 hmSmall' hbSolved
      (_root_.RoundComposite.unitCarryPackets m b (b + (b + 1)))
      hpackets.1
      hpackets.2.1
      (fun packet hp => (hpackets.2.2 packet hp).1)
      (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)
      rfl
      hSlack
  simpa [show b + (b + 1) = 2 * b + 1 by omega] using hSolved

theorem odd_successor_small_modulus_base_tail_of_slackPacketLiftAdd
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmallPacket)
    hb5 hmodd hm3 hmSmall hb

theorem oddSuccessorClosureGoal_of_high_and_slackPacketLift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall hHigh
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift hSmallPacket)

theorem odd_successor_closure_of_high_and_slackPacketLift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_high_and_slackPacketLift hHigh hSmallPacket)
    hb5 hmodd hm3 hb

theorem oddSuccessorClosureGoal_of_high_and_slackPacketLiftAdd
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall hHigh
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hSmallPacket)

theorem odd_successor_closure_of_high_and_slackPacketLiftAdd
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_high_and_slackPacketLiftAdd hHigh hSmallPacket)
    hb5 hmodd hm3 hb

theorem oddCoreHighModulusPrefixCountGoal_of_prefixCount
    (hParts : PrefixCount.AdmissiblePartsCountBranchGoal)
    (hLayers : PrefixCountLayerRealizationGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal := by
  intro d m hdodd hd5 hmodd hdm
  have hd2 : 2 ≤ d := by omega
  rcases hParts hdodd hmodd hd5 hdm with ⟨C, hC⟩
  rcases hLayers hd2 C hC with ⟨L⟩
  exact hGeom hd2 hdodd hd5 hmodd hdm hC L

theorem prefixCountGeometricCriterionGoal_of_rootFlat
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hLift : PrefixCountRootFlatCayleyLiftGoal) :
    PrefixCountGeometricCriterionGoal := by
  intro d m hd2 C hdodd hd5 hmodd hdm hC L
  haveI : NeZero m := ⟨by omega⟩
  rcases hReturn hd2 hdodd hd5 hmodd hdm hC L with ⟨cert⟩
  exact hLift hd2 hdodd hd5 hmodd hdm
    (Shared.rootFlatLayeredDecomposition_of_certificate cert)

theorem standardCayleySolved_of_rootFlatLayeredEquiv
    {d m : Nat} [NeZero m] {RootState : Type*}
    (D : Shared.RootFlatLayeredDecomposition (Fin d) (Fin d) RootState m)
    (E : ZMod m × RootState ≃ Shared.TorusVertex d m)
    (hCompat : RootFlatCayleyStepCompatible D E) :
    StandardCayleySolved d m := by
  let colorDir : Shared.TorusColor d → Shared.TorusVertex d m →
      Shared.TorusDirection d :=
    fun c x => D.schedule.dir (E.symm x).1 (E.symm x).2 c
  refine ⟨{
    colorDir := colorDir
    edgePartition := ?_
    colorHamiltonian := ?_
  }⟩
  · intro x i
    rcases D.edgePartition (E.symm x).1 (E.symm x).2 i with
      ⟨c, hc, huniq⟩
    exact ⟨c, hc, fun c' hc' => huniq c' hc'⟩
  · intro c
    refine Shared.single_cycle_of_equiv_conj E
      (Shared.cayleyColorStep colorDir c)
      (D.schedule.fullStep c)
      (D.colorHamiltonian c) ?_
    intro tw
    calc
      E.symm (Shared.cayleyColorStep colorDir c (E tw))
          = E.symm (E (D.schedule.fullStep c tw)) := by
              rw [hCompat c tw]
      _ = D.schedule.fullStep c tw := by simp

theorem standardCayleySolved_of_rootFlatLayered_standardStepSucc
    {n m : Nat} [NeZero m]
    (D : Shared.RootFlatLayeredDecomposition
      (Fin (n + 1)) (Fin (n + 1)) (Fin n → ZMod m) m)
    (hStep : D.schedule.step = prefixCountRootStepSucc) :
    StandardCayleySolved (n + 1) m := by
  refine standardCayleySolved_of_rootFlatLayeredEquiv D
    (prefixCountRootLayerEquivSucc n m) ?_
  intro c tw
  simp [Shared.RootFlatSchedule.fullStep, Shared.RootFlatSchedule.layerMap,
    Shared.cayleyColorStep, hStep, prefixCountRootLayerEquivSucc_step]

theorem standardCayleySolved_of_rootFlatLayered_standardStep
    {d m : Nat} [NeZero m] (hd1 : 1 ≤ d)
    (D : Shared.RootFlatLayeredDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m)
    (hStep : D.schedule.step = prefixCountRootStep d m) :
    StandardCayleySolved d m := by
  refine standardCayleySolved_of_rootFlatLayeredEquiv D
    (prefixCountRootLayerEquiv d m hd1) ?_
  intro c tw
  simp [Shared.RootFlatSchedule.fullStep, Shared.RootFlatSchedule.layerMap,
    Shared.cayleyColorStep, hStep, prefixCountRootLayerEquiv_step]

theorem prefixCountGeometricCriterionGoal_of_rootFlatCanonical
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    PrefixCountGeometricCriterionGoal := by
  intro d m hd2 C hdodd hd5 hmodd hdm hC L
  haveI : NeZero m := ⟨by omega⟩
  rcases hReturn hd2 hdodd hd5 hmodd hdm hC L with ⟨cert, hStep⟩
  let D : Shared.RootFlatLayeredDecomposition
      (Fin d) (Fin d) (PrefixCountRootState d m) m := {
    schedule := cert.schedule
    edgePartition := cert.schedule.edgePartition_of_rowLatin cert.rowLatin
    colorHamiltonian := cert.schedule.fullStepsHamiltonian_of_return
      cert.layerBijective cert.returnsSingleCycle
  }
  exact standardCayleySolved_of_rootFlatLayered_standardStep
    (by omega : 1 ≤ d) D hStep

theorem prefixCountRootFlatCayleyLiftGoal_of_equiv
    (hEquiv : PrefixCountRootFlatEquivLiftGoal) :
    PrefixCountRootFlatCayleyLiftGoal := by
  intro d m _inst hd2 hdodd hd5 hmodd hdm hRoot
  rcases hRoot with ⟨D⟩
  rcases hEquiv hd2 hdodd hd5 hmodd hdm D with ⟨E, hCompat⟩
  exact standardCayleySolved_of_rootFlatLayeredEquiv D E hCompat

theorem prefixCountLayerRealizationGoal_of_matrixLayerRealization
    (hMatrix : PrefixCount.MatrixLayerRealizationGoal) :
    PrefixCountLayerRealizationGoal := by
  intro d m hd2 C hC
  exact PrefixCount.layerRealization_of_matrixLayerRealizationGoal
    hMatrix hd2 C hC

theorem prefixCountLayerRealizationGoal_of_balancedMatrixLayerRealization
    (hBalanced : PrefixCount.BalancedMatrixLayerRealizationGoal) :
    PrefixCountLayerRealizationGoal :=
  prefixCountLayerRealizationGoal_of_matrixLayerRealization
    (PrefixCount.matrixLayerRealizationGoal_of_balanced hBalanced)

theorem prefixCountLayerRealizationGoal : PrefixCountLayerRealizationGoal :=
  prefixCountLayerRealizationGoal_of_matrixLayerRealization
    PrefixCount.matrixLayerRealizationGoal

theorem oddCoreHighModulusPrefixCountGoal_of_parts_and_geometry
    (hParts : PrefixCount.AdmissiblePartsCountBranchGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_prefixCount
    hParts prefixCountLayerRealizationGoal hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry
    (hQge2 : PrefixCount.TransportQge2Goal)
    (hQeq1 : PrefixCount.TransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_parts_and_geometry
    (PrefixCount.admissiblePartsCountBranchGoal_of_transports hQge2 hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry
    (PrefixCount.transportQge2Goal_of_margin hQge2)
    (PrefixCount.transportQeq1Goal_of_margin hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1Goal_of_compatible
      (PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne
        (PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily hQeq1)))
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1PlusFamily_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1PlusFamily_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    (PrefixCount.marginTransportQeq1Goal_of_compatible hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2OrdinaryCore_qeq1Compat_and_rootFlatCanonical
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
    (PrefixCount.marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
      hQge2)
    hQeq1 hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_geometry
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
    (PrefixCount.marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
      hQge2)
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
      hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Core_and_geometry
    (hQge2Plan : PrefixCount.OrdinaryQge2PlanGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_geometry
    (PrefixCount.ordinaryQge2SignedCoreGoal_of_plan_and_matrix
      hQge2Plan hQge2Matrix)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Core_and_geometry
    PrefixCount.ordinaryQge2PlanGoal hQge2Matrix hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_geometry
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
    hQge2Matrix
    (PrefixCount.ordinaryQeq1SignedCoreGoal_of_canonicalMatrix hQeq1Matrix)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_geometry
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_geometry
    (PrefixCount.ordinaryQge2SignedMatrixGoal_of_signedSeedClosure
      hQge2Closure)
    hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_geometry
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Correction : PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_geometry
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalMatrixGoal_of_correction
      hQeq1Correction)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_planMatrixSignedCores_and_geometry
    (hQge2Plan : PrefixCount.OrdinaryQge2PlanGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Plan : PrefixCount.OrdinaryQeq1PlanGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Core_and_geometry
    hQge2Plan hQge2Matrix
    (PrefixCount.ordinaryQeq1SignedCoreGoal_of_plan_and_matrix
      hQeq1Plan hQeq1Matrix)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Matrix_and_geometry
    (hQge2Plan : PrefixCount.OrdinaryQge2PlanGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_planMatrixSignedCores_and_geometry
    hQge2Plan hQge2Matrix
    PrefixCount.ordinaryQeq1PlanGoal hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedMatrix_qeq1Matrix_and_geometry
    (hQge2Seed : PrefixCount.OrdinaryQge2SeedGoal)
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Matrix_and_geometry
    (PrefixCount.ordinaryQge2PlanGoal_of_seed hQge2Seed)
    hQge2Matrix hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Matrix_and_geometry
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedMatrix_qeq1Matrix_and_geometry
    PrefixCount.ordinaryQge2SeedGoal hQge2Matrix hQeq1Matrix hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_rootFlatCanonical
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2OrdinaryCore_qeq1Compat_and_rootFlatCanonical
    hQge2
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
      hQeq1)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_rootFlatCanonical
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
    hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_rootFlatCanonical
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_geometry
    hQge2Matrix hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_geometry
    hQge2Closure hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Correction : PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_geometry
    hQge2Closure hQeq1Correction
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1CorrectionData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxMatching_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Aux : PrefixCount.OrdinaryQeq1AuxMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1CorrectionData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
      hQeq1Aux hQeq1Match)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1CorrectionData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData
      hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxPRowSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_pRowSpecialMatchingData
      hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxTargetHallDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxPRowSpecialMatchingDataGoal_of_targetHallData
      hQeq1Data)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1DegreeSpecialMatching_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1DegreeSpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_degreeSpecialMatching
      hQeq1Match)
    hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1DegreeMatching_and_rootFlatCanonical
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Degree : PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxMatching_and_rootFlatCanonical
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxMatrixGoal_of_degreeMatrix hQeq1Degree)
    hQeq1Match hReturn

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Margin_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
    (PrefixCount.marginTransportQge2Goal_of_plan hQge2)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Compat_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Margin_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1Goal_of_compatible hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1MatchedPMOne_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1MatchedPMOneGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Compat_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1MatchedPMOne_and_geometry
    hQge2
    (PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily hQeq1)
    hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry
    hQge2 hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry
    (PrefixCount.marginTransportQge2PlanGoal_of_plan_and_matrix
      hQge2Plan hQge2Matrix)
    hQeq1 hGeom

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlat
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hLift : PrefixCountRootFlatCayleyLiftGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry
    hQge2Plan hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlat hReturn hLift)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlatEquiv
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hEquiv : PrefixCountRootFlatEquivLiftGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlat
    hQge2Plan hQge2Matrix hQeq1 hReturn
    (prefixCountRootFlatCayleyLiftGoal_of_equiv hEquiv)

theorem oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlatCanonical
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry
    hQge2Plan hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)

theorem d11SmallModulusLiftFromD5Base_of_goal
    (hSmall11 : D11SmallModulusFromD5BaseGoal) :
    D11SmallModulusLiftFromD5Base StandardCayleySolved := by
  intro m hm3 hmodd hm11 h5
  exact hSmall11 hm3 hmodd hm11 h5

theorem oddCoreSmallModulusLiftOfBase_of_goal
    (hSmallLift : OddCoreSmallModulusOfBaseGoal) :
    OddCoreSmallModulusLiftOfBase StandardCayleySolved := by
  intro d m b hdodd hd13 hmodd hm3 hmd hbSolved hbRange
  exact hSmallLift hdodd hd13 hmodd hm3 hmd hbSolved hbRange

theorem oddCoreSmallModulusOfBaseGoal_of_unitPackets
    (hPacketLift : OddCoreSmallModulusOfUnitPacketsGoal) :
    OddCoreSmallModulusOfBaseGoal := by
  intro d m b hdodd hd13 hmodd hm3 hmd hbSolved hbRange
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec hm3 hmodd hbRange
  exact hPacketLift hdodd hd13 hmodd hm3 hmd hbSolved
    (_root_.RoundComposite.unitCarryPackets m b d)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)

theorem d11SmallModulusFromD5BaseGoal_of_smallUnitPacketLift
    (hSmallPacket : OddCoreSmallModulusUnitPacketLiftGoal) :
    D11SmallModulusFromD5BaseGoal := by
  intro m hm3 hmodd hm11 h5
  have hrange : 2 * 5 < 11 ∧ 11 ≤ 3 * 5 := by omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := 5) (d := 11) (m := m) hm3 hmodd hrange
  exact hSmallPacket
    (by decide : Odd 11)
    (by decide : 11 ≤ 11)
    hmodd hm3 hm11 h5
    (_root_.RoundComposite.unitCarryPackets m 5 11)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)

theorem oddCoreSmallModulusOfBaseGoal_of_smallUnitPacketLift
    (hSmallPacket : OddCoreSmallModulusUnitPacketLiftGoal) :
    OddCoreSmallModulusOfBaseGoal := by
  intro d m b hdodd hd13 hmodd hm3 hmd hbSolved hbRange
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec hm3 hmodd hbRange
  exact hSmallPacket hdodd (by omega) hmodd hm3 hmd hbSolved
    (_root_.RoundComposite.unitCarryPackets m b d)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)

theorem d11SmallModulusFromD5BaseGoal_of_slackPacketLift
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    D11SmallModulusFromD5BaseGoal := by
  intro m hm3 hmodd hm11 h5
  have hrange : 2 * 5 < 11 ∧ 11 ≤ 3 * 5 := by omega
  have hpackets :=
    _root_.RoundComposite.unitCarryPackets_spec
      (b := 5) (d := 11) (m := m) hm3 hmodd hrange
  have hTail : 11 - 5 > 5 := by omega
  have hpow4 : 66 < m ^ 4 := by
    have hmono : 3 ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left hm3 4
    norm_num at hmono ⊢
    omega
  have hSlack : m ^ 5 > m * 11 * (11 - 5) := by
    have hmpos : 0 < m := by omega
    have hmul : m * 66 < m * (m ^ 4) :=
      Nat.mul_lt_mul_of_pos_left hpow4 hmpos
    nlinarith
  exact hSmallPacket
    (by decide : Odd 11)
    (by decide : 11 ≤ 11)
    hmodd hm3 hm11 h5
    (_root_.RoundComposite.unitCarryPackets m 5 11)
    hpackets.1
    hpackets.2.1
    (fun packet hp => (hpackets.2.2 packet hp).1)
    (fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha)
    hTail hSlack

theorem oddCoreSmallGE13_of_slackPacketLift
    (hBaseSlack : OddCoreSmallBaseSlackWitnessGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal) :
    OddCoreSmallGE13 StandardCayleySolved := by
  intro d m hd13 hdodd hm3 hmodd hmd
  rcases hBaseSlack hdodd hd13 hmodd hm3 hmd with
    ⟨w, hTail, hSlack⟩
  exact hSmallPacket hdodd (by omega) hmodd hm3 hmd
    (standard_cayley_odd_uniform_of_seed_semigroup w.seed hm3 hmodd)
    w.packets
    w.packets_length
    w.packets_total_length
    w.packet_sum
    w.packet_units
    hTail
    hSlack

theorem oddCoreHighGE13_of_prefix_count
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved) :
    OddCoreHighGE13 StandardCayleySolved := by
  intro d m hd13 hdodd hm3 hmodd hdm
  exact hHigh hdodd (by omega) hm3 hmodd hdm

theorem standard_cayley_odd_uniform_11_of_high_and_d5_base_tail
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved)
    (hSmall11 : D11SmallModulusLiftFromD5Base StandardCayleySolved) :
    OddUniformSolved StandardCayleySolved 11 := by
  intro m hm3 hmodd
  by_cases hm11 : 11 ≤ m
  · exact hHigh (by decide : Odd 11) (by decide : 5 ≤ 11) hm3 hmodd hm11
  · exact hSmall11 hm3 hmodd (lt_of_not_ge hm11)
      (standard_cayley_odd_uniform_5 hm3 hmodd)

theorem oddCoreSmallGE13_of_seed_semigroup_base
    (hLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved) :
    OddCoreSmallGE13 StandardCayleySolved := by
  intro d m hd13 hdodd hm3 hmodd hmd
  rcases seed_semigroup_base_available hdodd hd13 with
    ⟨b, hbSeed, hbRange⟩
  exact hLift hdodd hd13 hmodd hm3 hmd
    (standard_cayley_odd_uniform_of_seed_semigroup hbSeed hm3 hmodd)
    hbRange

theorem standard_cayley_odd_uniform_9_of_3 :
    OddUniformSolved StandardCayleySolved 9 := by
  intro m hm3 hmodd
  simpa using
    (odd_uniform_cayley_mul_of_standard
      (a := 3) (b := 3) (by decide) (by decide)
      standard_cayley_odd_uniform_3 standard_cayley_odd_uniform_3
      (m := m) hm3 hmodd)

theorem odd_modulus_tori_odd_dimension_core_of_branches
    (hD11 : OddUniformSolved StandardCayleySolved 11)
    (hHigh : OddCoreHighGE13 StandardCayleySolved)
    (hSmall : OddCoreSmallGE13 StandardCayleySolved)
    {d : Nat} (hdodd : Odd d) (hd3 : 3 ≤ d) :
    OddUniformSolved StandardCayleySolved d := by
  intro m hm3 hmodd
  by_cases h3 : d = 3
  · subst d
    exact standard_cayley_odd_uniform_3 hm3 hmodd
  by_cases h5 : d = 5
  · subst d
    exact standard_cayley_odd_uniform_5 hm3 hmodd
  by_cases h7 : d = 7
  · subst d
    exact standard_cayley_odd_uniform_7 hm3 hmodd
  by_cases h9 : d = 9
  · subst d
    exact standard_cayley_odd_uniform_9_of_3 hm3 hmodd
  by_cases h11 : d = 11
  · subst d
    exact hD11 hm3 hmodd
  have hd13 : 13 ≤ d := by
    rcases hdodd with ⟨k, hk⟩
    omega
  by_cases hdm : d ≤ m
  · exact hHigh hd13 hdodd hm3 hmodd hdm
  · exact hSmall hd13 hdodd hm3 hmodd (lt_of_not_ge hdm)

theorem odd_modulus_tori_all_dimensions_of_odd_core_branches
    (hD11 : OddUniformSolved StandardCayleySolved 11)
    (hHigh : OddCoreHighGE13 StandardCayleySolved)
    (hSmall : OddCoreSmallGE13 StandardCayleySolved)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_odd_core
    (fun hd3 hdodd =>
      odd_modulus_tori_odd_dimension_core_of_branches
        hD11 hHigh hSmall hdodd hd3)
    hd2 hmodd hm3

theorem odd_modulus_tori_odd_dimension_core_of_refined_branches
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved)
    (hD11Small : D11SmallModulusLiftFromD5Base StandardCayleySolved)
    (hSmallLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved)
    {d : Nat} (hdodd : Odd d) (hd3 : 3 ≤ d) :
    OddUniformSolved StandardCayleySolved d :=
  odd_modulus_tori_odd_dimension_core_of_branches
    (standard_cayley_odd_uniform_11_of_high_and_d5_base_tail
      hHigh hD11Small)
    (oddCoreHighGE13_of_prefix_count hHigh)
    (oddCoreSmallGE13_of_seed_semigroup_base hSmallLift)
    hdodd hd3

theorem odd_modulus_tori_all_dimensions_of_refined_branches
    (hHigh : OddCoreHighModulusPrefixCount StandardCayleySolved)
    (hD11Small : D11SmallModulusLiftFromD5Base StandardCayleySolved)
    (hSmallLift : OddCoreSmallModulusLiftOfBase StandardCayleySolved)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_odd_core
    (fun hd3 hdodd =>
      odd_modulus_tori_odd_dimension_core_of_refined_branches
        hHigh hD11Small hSmallLift hdodd hd3)
    hd2 hmodd hm3

theorem odd_modulus_tori_odd_dimension_core_of_main_lemmas
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hD11Small : D11SmallModulusFromD5BaseGoal)
    (hSmallLift : OddCoreSmallModulusOfBaseGoal)
    {d : Nat} (hdodd : Odd d) (hd3 : 3 ≤ d) :
    OddUniformSolved StandardCayleySolved d :=
  odd_modulus_tori_odd_dimension_core_of_refined_branches
    (oddCoreHighModulusPrefixCount_of_goal hHigh)
    (d11SmallModulusLiftFromD5Base_of_goal hD11Small)
    (oddCoreSmallModulusLiftOfBase_of_goal hSmallLift)
    hdodd hd3

theorem odd_modulus_tori_all_dimensions_of_main_lemmas
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hD11Small : D11SmallModulusFromD5BaseGoal)
    (hSmallLift : OddCoreSmallModulusOfBaseGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_refined_branches
    (oddCoreHighModulusPrefixCount_of_goal hHigh)
    (d11SmallModulusLiftFromD5Base_of_goal hD11Small)
    (oddCoreSmallModulusLiftOfBase_of_goal hSmallLift)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_high_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusUnitPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_main_lemmas
    hHigh
    (d11SmallModulusFromD5BaseGoal_of_smallUnitPacketLift hSmallPacket)
    (oddCoreSmallModulusOfBaseGoal_of_smallUnitPacketLift hSmallPacket)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_odd_core_branches
    (standard_cayley_odd_uniform_11_of_high_and_d5_base_tail
      (oddCoreHighModulusPrefixCount_of_goal hHigh)
      (d11SmallModulusLiftFromD5Base_of_goal
        (d11SmallModulusFromD5BaseGoal_of_slackPacketLift hSmallPacket)))
    (oddCoreHighGE13_of_prefix_count
      (oddCoreHighModulusPrefixCount_of_goal hHigh))
    (oddCoreSmallGE13_of_slackPacketLift
      oddCoreSmallBaseSlackWitnessGoal_of_seed_semigroup hSmallPacket)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_357_and_successor
    (oddSuccessorClosureGoal_of_high_and_successorSmall hHigh hSmall)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmall hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_slackPacketLift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical
    hQge2 hQeq1 hReturn
    (oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLift hSmallPacket)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_ordinarySignedCores_rootFlatCanonical_and_slackPacketLift
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_slackPacketLift
    (PrefixCount.marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
      hQge2)
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
      hQeq1)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_ordinarySignedCores_geometry_and_slackPacketLift
    (hQge2 : PrefixCount.OrdinaryQge2SignedCoreGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_geometry_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
      hQge2Matrix hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_rootFlatCanonical_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1 : PrefixCount.OrdinaryQeq1SignedCoreGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_geometry_and_slackPacketLift
    hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_geometry_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_geometry_and_slackPacketLift
    hQge2Matrix
    (PrefixCount.ordinaryQeq1SignedCoreGoal_of_canonicalMatrix hQeq1Matrix)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_geometry_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_geometry_and_slackPacketLift
    (PrefixCount.ordinaryQge2SignedMatrixGoal_of_signedSeedClosure
      hQge2Closure)
    hQeq1Matrix hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_geometry_and_slackPacketLift
    hQge2Matrix hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1CanonicalMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_geometry_and_slackPacketLift
    hQge2Closure hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Correction_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Correction : PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalMatrixGoal_of_correction
      hQeq1Correction)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Correction_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxMatching_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Aux : PrefixCount.OrdinaryQeq1AuxMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
      hQeq1Aux hQeq1Match)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData
      hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxPRowSpecialMatchingDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_pRowSpecialMatchingData
      hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxTargetHallData_rootFlatCanonical_and_slackPacketLift
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Data : PrefixCount.OrdinaryQeq1AuxTargetHallDataGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxPRowSpecialMatchingDataGoal_of_targetHallData
      hQeq1Data)
    hReturn hSmallPacket hd2 hmodd hm3

def OddModulusToriV4ConstructionBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4JointMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4PRowMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxPRowSpecialMatchingDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4TargetHallBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxTargetHallDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4DegreeSpecialMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1DegreeSpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem not_oddModulusToriV4DegreeSpecialMatchingBlocksGoal :
    ¬ OddModulusToriV4DegreeSpecialMatchingBlocksGoal := by
  intro hBlocks
  exact PrefixCount.not_ordinaryQeq1DegreeSpecialMatchingGoal hBlocks.2.1

def OddModulusToriV4PreferredBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ProperCutBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ScheduleBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ScheduleAddBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddCoreSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4SuccessorScheduleBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

def OddModulusToriV4SuccessorScheduleAddBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal ∧
  OddSuccessorSmallModulusSlackPacketLiftAddGoal

def OddModulusToriV4DegreeMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4UniformDegreeBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeArithmeticGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4UniformTotalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeTotalGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4PostTotalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4ResidueBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeResidueCountGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4IntervalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeIntervalPartitionGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

def OddModulusToriV4PostUniformBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem odd_modulus_tori_all_dimensions_of_v4_construction_blocks
    (hBlocks : OddModulusToriV4ConstructionBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_joint_matching_blocks
    (hBlocks : OddModulusToriV4JointMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_pRow_matching_blocks
    (hBlocks : OddModulusToriV4PRowMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxPRowSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_targetHall_blocks
    (hBlocks : OddModulusToriV4TargetHallBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Data, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxTargetHallData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure hQeq1Data hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_degree_special_matching_blocks
    (hBlocks : OddModulusToriV4DegreeSpecialMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with ⟨hQge2Closure, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxSpecialMatchingData_rootFlatCanonical_and_slackPacketLift
      hQge2Closure
      (PrefixCount.ordinaryQeq1AuxSpecialMatchingDataGoal_of_degreeSpecialMatching
        hQeq1Match)
      hReturn hSmallPacket hd2 hmodd hm3

theorem oddCoreHighModulusPrefixCountGoal_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal := by
  rcases hBlocks with ⟨hQge2Closure, hReturn, _hSmallPacket⟩
  exact
    oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
      hQge2Closure PrefixCount.ordinaryQeq1AuxTargetHallDataGoal hReturn

theorem odd_successor_small_modulus_base_tail_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m := by
  rcases hBlocks with ⟨_hQge2Closure, _hReturn, hSmallPacket⟩
  exact odd_successor_small_modulus_base_tail_of_slackPacketLift
    hSmallPacket hb5 hmodd hm3 hmSmall hb

theorem oddSuccessorClosureGoal_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal) :
    OddSuccessorClosureGoal := by
  rcases hBlocks with ⟨hQge2Closure, hReturn, hSmallPacket⟩
  exact oddSuccessorClosureGoal_of_high_and_slackPacketLift
    (oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
      hQge2Closure PrefixCount.ordinaryQeq1AuxTargetHallDataGoal hReturn)
    hSmallPacket

theorem odd_successor_closure_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_preferred_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_modulus_tori_all_dimensions_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  let targetHallBlocks : OddModulusToriV4TargetHallBlocksGoal :=
    ⟨hBlocks.1, PrefixCount.ordinaryQeq1AuxTargetHallDataGoal,
      hBlocks.2.1, hBlocks.2.2⟩
  odd_modulus_tori_all_dimensions_of_v4_targetHall_blocks
    targetHallBlocks hd2 hmodd hm3

theorem oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal) :
    OddModulusToriV4PreferredBlocksGoal :=
  ⟨PrefixCount.ordinaryQge2SignedSeedClosureGoal_of_properCutClosure
      hBlocks.1,
    hBlocks.2.1, hBlocks.2.2⟩

theorem oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddModulusToriV4ProperCutBlocksGoal :=
  ⟨hBlocks.1,
    prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion hBlocks.2.1,
    hBlocks.2.2⟩

theorem oddModulusToriV4PreferredBlocksGoal_of_scheduleBlocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddModulusToriV4PreferredBlocksGoal :=
  oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)

theorem oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4ScheduleBlocksGoal :=
  ⟨hBlocks.1, hBlocks.2.1,
    oddCoreSmallModulusSlackPacketLiftGoal_of_add hBlocks.2.2⟩

theorem oddModulusToriV4ProperCutBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4ProperCutBlocksGoal :=
  oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddModulusToriV4PreferredBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4PreferredBlocksGoal :=
  oddModulusToriV4PreferredBlocksGoal_of_scheduleBlocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4SuccessorScheduleAddBlocksGoal :=
  ⟨hBlocks.1, hBlocks.2.1,
    oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_coreAdd hBlocks.2.2⟩

theorem oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal) :
    OddModulusToriV4SuccessorScheduleBlocksGoal :=
  ⟨hBlocks.1, hBlocks.2.1,
    oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd hBlocks.2.2⟩

theorem oddModulusToriV4SuccessorScheduleBlocksGoal_of_scheduleAddBlocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddModulusToriV4SuccessorScheduleBlocksGoal :=
  oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
    (oddModulusToriV4SuccessorScheduleAddBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddSuccessorClosureGoal_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)

theorem oddSuccessorClosureGoal_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)

theorem oddSuccessorClosureGoal_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem odd_successor_closure_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_properCut_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_schedule_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_scheduleAdd_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_modulus_tori_all_dimensions_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)
    hd2 hmodd hm3

theorem oddCoreHighModulusPrefixCountGoal_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
    (PrefixCount.ordinaryQge2SignedSeedClosureGoal_of_properCutClosure hBlocks.1)
    PrefixCount.ordinaryQeq1AuxTargetHallDataGoal
    (prefixCountRootFlatCanonicalReturnGoal_of_scheduleCriterion hBlocks.2.1)

theorem oddCoreHighModulusPrefixCountGoal_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal) :
    OddCoreHighModulusPrefixCountGoal :=
  oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)

theorem oddSuccessorClosureGoal_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_high_and_successorSmall
    (oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks hBlocks)
    hBlocks.2.2

theorem oddSuccessorClosureGoal_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)

theorem odd_successor_closure_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_successorSchedule_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_successor_closure_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  (oddSuccessorClosureGoal_of_v4_successorScheduleAdd_blocks hBlocks)
    hb5 hmodd hm3 hb

theorem odd_modulus_tori_all_dimensions_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (oddCoreHighModulusPrefixCountGoal_of_v4_successorSchedule_blocks hBlocks)
    hBlocks.2.2
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_successorSchedule
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorSchedule_blocks
    ⟨hQge2Proper, hSchedule, hSmall⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_successorScheduleAdd_blocks
    ⟨hQge2Proper, hSchedule, hSmall⟩
    hd2 hmodd hm3

theorem odd_successor_small_modulus_base_tail_of_v4_properCut_blocks
    (hBlocks : OddModulusToriV4ProperCutBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_preferred_blocks
    (oddModulusToriV4PreferredBlocksGoal_of_properCutBlocks hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_schedule_blocks
    (hBlocks : OddModulusToriV4ScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_properCut_blocks
    (oddModulusToriV4ProperCutBlocksGoal_of_scheduleBlocks hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_scheduleAdd_blocks
    (hBlocks : OddModulusToriV4ScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_schedule_blocks
    (oddModulusToriV4ScheduleBlocksGoal_of_scheduleAddBlocks hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_successorSchedule_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  hBlocks.2.2 hb5 hmodd hm3 hmSmall hb

theorem odd_successor_small_modulus_base_tail_of_v4_successorScheduleAdd_blocks
    (hBlocks : OddModulusToriV4SuccessorScheduleAddBlocksGoal)
    {b m : Nat}
    (hb5 : 5 ≤ b)
    (hmodd : Odd m) (hm3 : 3 ≤ m)
    (hmSmall : m < 2 * b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m :=
  odd_successor_small_modulus_base_tail_of_v4_successorSchedule_blocks
    (oddModulusToriV4SuccessorScheduleBlocksGoal_of_successorScheduleAddBlocks
      hBlocks)
    hb5 hmodd hm3 hmSmall hb

theorem odd_modulus_tori_all_dimensions_of_qeq1DegreeMatching
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Degree : PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v4_construction_blocks
    ⟨hQge2Closure,
      PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
        (PrefixCount.ordinaryQeq1AuxMatrixGoal_of_degreeMatrix hQeq1Degree)
        hQeq1Match,
      hReturn,
      hSmallPacket⟩
    hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1UniformDegree
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Arith : PrefixCount.OrdinaryQeq1AuxDegreeArithmeticGoal)
    (hQeq1Uniform : PrefixCount.UniformColumnDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1DegreeMatching
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxDegreeMatrixGoal_of_uniformColumnDegree
      hQeq1Arith hQeq1Uniform)
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1UniformTotal
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Total : PrefixCount.OrdinaryQeq1AuxDegreeTotalGoal)
    (hQeq1Uniform : PrefixCount.UniformColumnDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1UniformDegree
    hQge2Closure
    (PrefixCount.ordinaryQeq1AuxDegreeArithmeticGoal_of_total hQeq1Total)
    hQeq1Uniform hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1PostTotal
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Uniform : PrefixCount.UniformColumnDegreeMatrixGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1UniformTotal
    hQge2Closure PrefixCount.ordinaryQeq1AuxDegreeTotalGoal
    hQeq1Uniform hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1ResidueCount
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Residue : PrefixCount.UniformColumnDegreeResidueCountGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1PostTotal
    hQge2Closure
    (PrefixCount.uniformColumnDegreeMatrixGoal_of_residueCount hQeq1Residue)
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1IntervalPartition
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Partition : PrefixCount.UniformColumnDegreeIntervalPartitionGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1ResidueCount
    hQge2Closure
    (PrefixCount.uniformColumnDegreeResidueCountGoal_of_intervalPartition
      hQeq1Partition)
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qeq1PostUniform
    (hQge2Closure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal)
    (hQeq1Match : PrefixCount.OrdinaryQeq1SpecialMatchingGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qeq1IntervalPartition
    hQge2Closure PrefixCount.uniformColumnDegreeIntervalPartitionGoal
    hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_degree_matching_blocks
    (hBlocks : OddModulusToriV4DegreeMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Degree, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1DegreeMatching
      hQge2Closure hQeq1Degree hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_uniform_degree_blocks
    (hBlocks : OddModulusToriV4UniformDegreeBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Arith, hQeq1Uniform,
      hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1UniformDegree
      hQge2Closure hQeq1Arith hQeq1Uniform
      hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_uniform_total_blocks
    (hBlocks : OddModulusToriV4UniformTotalBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Total, hQeq1Uniform,
      hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1UniformTotal
      hQge2Closure hQeq1Total hQeq1Uniform
      hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_post_total_blocks
    (hBlocks : OddModulusToriV4PostTotalBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Uniform, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1PostTotal
      hQge2Closure hQeq1Uniform hQeq1Match
      hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_residue_blocks
    (hBlocks : OddModulusToriV4ResidueBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Residue, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1ResidueCount
      hQge2Closure hQeq1Residue hQeq1Match
      hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_interval_blocks
    (hBlocks : OddModulusToriV4IntervalBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Partition, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1IntervalPartition
      hQge2Closure hQeq1Partition hQeq1Match
      hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_v4_post_uniform_blocks
    (hBlocks : OddModulusToriV4PostUniformBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  rcases hBlocks with
    ⟨hQge2Closure, hQeq1Match, hReturn, hSmallPacket⟩
  exact
    odd_modulus_tori_all_dimensions_of_qeq1PostUniform
      hQge2Closure hQeq1Match hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_geometry_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Matrix_and_geometry
      hQge2Matrix hQeq1Matrix hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_rootFlatCanonical_and_slackPacketLift
    (hQge2Matrix : PrefixCount.OrdinaryQge2SignedMatrixGoal)
    (hQeq1Matrix : PrefixCount.OrdinaryQeq1SignedMatrixGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_geometry_and_slackPacketLift
    hQge2Matrix hQeq1Matrix
    (prefixCountGeometricCriterionGoal_of_rootFlatCanonical hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_transports_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.TransportQge2Goal)
    (hQeq1 : PrefixCount.TransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_margins_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Margin_qeq1PlusFamily_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_geometry_and_small_packet_lift
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    hQeq1 hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (PrefixCount.marginTransportQge2Goal_of_compatible hQge2)
    hQeq1 hReturn hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_geometry
      hQge2 hQeq1 hGeom)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Compat_qeq1Compat_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Margin_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1Goal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_margins_geometry_and_small_packet_lift
    (PrefixCount.marginTransportQge2Goal_of_plan hQge2)
    hQeq1 hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Compat_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Margin_geometry_and_small_packet_lift
    hQge2
    (PrefixCount.marginTransportQeq1Goal_of_compatible hQeq1)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1MatchedPMOne_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1MatchedPMOneGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Compat_geometry_and_small_packet_lift
    hQge2
    (PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne hQeq1)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1MatchedPMOne_geometry_and_small_packet_lift
    hQge2
    (PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily hQeq1)
    hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_rootFlatCanonical
      hQge2 hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hGeom : PrefixCountGeometricCriterionGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_geometry_and_small_packet_lift
    (PrefixCount.marginTransportQge2PlanGoal_of_plan_and_matrix
      hQge2Plan hQge2Matrix)
    hQeq1 hGeom hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlat_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hLift : PrefixCountRootFlatCayleyLiftGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift
    hQge2Plan hQge2Matrix hQeq1
    (prefixCountGeometricCriterionGoal_of_rootFlat hReturn hLift)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatEquiv_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hEquiv : PrefixCountRootFlatEquivLiftGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlat_and_small_packet_lift
    hQge2Plan hQge2Matrix hQeq1 hReturn
    (prefixCountRootFlatCayleyLiftGoal_of_equiv hEquiv)
    hSmallPacket hd2 hmodd hm3

theorem odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlatCanonical
      hQge2Plan hQge2Matrix hQeq1 hReturn)
    hSmallPacket hd2 hmodd hm3

end Concrete
end RoundComposite
