import EvenV11.Basic

namespace EvenV11
namespace UnitCarry

abbrev additiveSkewMap {Base : Type*} {m : Nat}
    (baseStep : Base → Base) (carry : Base → ZMod m) :
    Base × ZMod m → Base × ZMod m :=
  Shared.skewProductMap baseStep (fun b z => z + carry b)

theorem unitCarrySingleCycle
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
  Shared.single_cycle_of_skewProduct_zmod_additive_unit_carry
    baseStep carry base period a hbase hreturnBase hbaseCover ha hcarry

theorem rankUnitCarrySingleCycle
    {Base : Type*} [Fintype Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (carry : Base → ZMod m) (base : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hunit : IsUnit (∑ x : Base, carry x)) :
    Shared.IsSingleCycleMap (additiveSkewMap baseStep carry) :=
  Shared.single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
    baseStep rank carry base hstep hunit

theorem rankUnitCarrySingleCycle_iff
    {Base : Type*} [Fintype Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (carry : Base → ZMod m) (base : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap (additiveSkewMap baseStep carry) ↔
      IsUnit (∑ x : Base, carry x) :=
  Shared.skewProduct_zmod_additive_rank_single_cycle_iff_unit_sum
    baseStep rank carry base hstep

def pointCarry {Base : Type*} [DecidableEq Base] {m : Nat}
    (crossing : Base) (a : ZMod m) : Base → ZMod m :=
  fun x => if x = crossing then a else 0

theorem pointCarry_crossing
    {Base : Type*} [DecidableEq Base] {m : Nat}
    (crossing : Base) (a : ZMod m) :
    pointCarry crossing a crossing = a := by
  simp [pointCarry]

theorem pointCarry_of_ne
    {Base : Type*} [DecidableEq Base] {m : Nat}
    {crossing x : Base} (a : ZMod m) (hx : x ≠ crossing) :
    pointCarry crossing a x = 0 := by
  simp [pointCarry, hx]

theorem pointCarrySum
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) (a : ZMod m) :
    (∑ x : Base, pointCarry crossing a x) = a := by
  simp [pointCarry]

theorem pointCarryUnit
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) {a : ZMod m} (ha : IsUnit a) :
    IsUnit (∑ x : Base, pointCarry crossing a x) := by
  rw [pointCarrySum crossing a]
  exact ha

theorem pointCarrySingleCycle
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base) (a : ZMod m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (ha : IsUnit a) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep (pointCarry crossing a)) :=
  letI : Fintype Base := Fintype.ofFinite Base
  rankUnitCarrySingleCycle baseStep rank (pointCarry crossing a)
    base hstep (pointCarryUnit crossing ha)

theorem singlePointCarry_eq_pointCarry
    {Base : Type*} [DecidableEq Base] {m : Nat} (crossing : Base) :
    (fun x : Base => if x = crossing then (1 : ZMod m) else 0) =
      pointCarry crossing (1 : ZMod m) :=
  rfl

theorem negativeSinglePointCarry_eq_pointCarry
    {Base : Type*} [DecidableEq Base] {m : Nat} (crossing : Base) :
    (fun x : Base => if x = crossing then (-1 : ZMod m) else 0) =
      pointCarry crossing (-1 : ZMod m) :=
  rfl

theorem singlePointCarrySingleCycle_pointCarry
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (pointCarry crossing (1 : ZMod m))) :=
  pointCarrySingleCycle baseStep rank base crossing
    (1 : ZMod m) hstep (by
      simp)

theorem negativeSinglePointCarrySingleCycle_pointCarry
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (pointCarry crossing (-1 : ZMod m))) :=
  pointCarrySingleCycle baseStep rank base crossing
    (-1 : ZMod m) hstep (by
      simp)

theorem singlePointCarrySum
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    (∑ x : Base, if x = crossing then (1 : ZMod m) else 0) = 1 := by
  simp

theorem negativeSinglePointCarrySum
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    (∑ x : Base, if x = crossing then (-1 : ZMod m) else 0) = -1 := by
  simp

theorem singlePointCarryUnit
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    IsUnit (∑ x : Base, if x = crossing then (1 : ZMod m) else 0) := by
  rw [singlePointCarrySum crossing]
  simp

theorem negativeSinglePointCarryUnit
    {Base : Type*} [Fintype Base] [DecidableEq Base]
    {m : Nat} (crossing : Base) :
    IsUnit (∑ x : Base, if x = crossing then (-1 : ZMod m) else 0) := by
  rw [negativeSinglePointCarrySum crossing]
  simp

theorem singlePointCarrySingleCycle
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (fun x : Base => if x = crossing then (1 : ZMod m) else 0)) :=
  letI : Fintype Base := Fintype.ofFinite Base
  rankUnitCarrySingleCycle baseStep rank
    (fun x : Base => if x = crossing then (1 : ZMod m) else 0)
    base hstep (by
      simp)

theorem negativeSinglePointCarrySingleCycle
    {Base : Type*} [Finite Base] [DecidableEq Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (fun x : Base => if x = crossing then (-1 : ZMod m) else 0)) :=
  letI : Fintype Base := Fintype.ofFinite Base
  rankUnitCarrySingleCycle baseStep rank
    (fun x : Base => if x = crossing then (-1 : ZMod m) else 0)
    base hstep (by
      simp)

theorem squareSubOneCoprimeSelf (m : Nat) [NeZero m] :
    Nat.Coprime (m * m - 1) m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmmpos : 0 < m * m := Nat.mul_pos hmpos hmpos
  have hle : 1 ≤ m * m := Nat.succ_le_of_lt hmmpos
  have hsq : Nat.Coprime (m * m - 1) (m * m) :=
    (Nat.coprime_self_sub_left hle).2 (by simp)
  exact Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right m m) hsq

theorem squareSubOneCoprimePow (m k : Nat) [NeZero m] :
    Nat.Coprime (m * m - 1) (m ^ k) :=
  (squareSubOneCoprimeSelf m).pow_right k

theorem squareSubOneUnitZModPow (m k : Nat) [NeZero m] :
    IsUnit (((m * m - 1 : Nat) : ZMod (m ^ k))) := by
  exact (ZMod.isUnit_iff_coprime (m * m - 1) (m ^ k)).2
    (squareSubOneCoprimePow m k)

theorem singletonExponentSum
    {Terminal : Type*} [Fintype Terminal] [DecidableEq Terminal]
    {M : Nat} (q0 : Terminal) :
    (∑ q : Terminal, if q = q0 then (1 : ZMod M) else 0) = 1 := by
  simp

theorem complementSingletonExponentSum
    {Terminal : Type*} [Fintype Terminal] [DecidableEq Terminal]
    {M : Nat} (q0 : Terminal) :
    (∑ q : Terminal, if q = q0 then (0 : ZMod M) else 1) =
      ((Fintype.card Terminal - 1 : Nat) : ZMod M) := by
  calc
    (∑ q : Terminal, if q = q0 then (0 : ZMod M) else 1)
        = ∑ q ∈ (Finset.univ : Finset Terminal),
            if q ≠ q0 then (1 : ZMod M) else 0 := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases h : q = q0
          · simp [h]
          · simp [h]
    _ = (((Finset.univ.filter (fun q : Terminal => q ≠ q0)).card : Nat) :
          ZMod M) := by
          rw [Finset.sum_boole]
    _ = ((Fintype.card Terminal - 1 : Nat) : ZMod M) := by
          have hcard :
              (Finset.univ.filter (fun q : Terminal => q ≠ q0)).card =
                Fintype.card Terminal - 1 := by
            calc
              (Finset.univ.filter (fun q : Terminal => q ≠ q0)).card =
                  (Finset.univ.erase q0).card := by
                    congr
                    ext q
                    simp [Finset.mem_erase, eq_comm]
              _ = Fintype.card Terminal - 1 := by
                    rw [Finset.card_erase_of_mem (Finset.mem_univ q0)]
                    rw [Finset.card_univ]
          rw [hcard]

abbrev productExponentMap {Terminal : Type*} {M : Nat}
    (terminalStep : Terminal → Terminal)
    (exponent : Terminal → ZMod M) :
    Terminal × ZMod M → Terminal × ZMod M :=
  additiveSkewMap terminalStep exponent

theorem productExponentSingleCycle
    {Terminal : Type*} [Fintype Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (exponent : Terminal → ZMod M) (base : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1)
    (hunit : IsUnit (∑ q : Terminal, exponent q)) :
    Shared.IsSingleCycleMap (productExponentMap terminalStep exponent) :=
  rankUnitCarrySingleCycle terminalStep terminalRank exponent base hstep hunit

theorem pointProductExponentSingleCycle
    {Terminal : Type*} [Finite Terminal] [DecidableEq Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (base q0 : Terminal) (a : ZMod M)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1)
    (ha : IsUnit a) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep (pointCarry q0 a)) :=
  pointCarrySingleCycle terminalStep terminalRank base q0 a hstep ha

theorem singletonPointProductExponentSingleCycle
    {Terminal : Type*} [Finite Terminal] [DecidableEq Terminal]
    {N M : Nat} [NeZero N] [NeZero M]
    (terminalStep : Terminal → Terminal)
    (terminalRank : Terminal ≃ ZMod N)
    (base q0 : Terminal)
    (hstep : ∀ q : Terminal,
      terminalRank (terminalStep q) = terminalRank q + 1) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (pointCarry q0 (1 : ZMod M))) :=
  pointProductExponentSingleCycle terminalStep terminalRank base q0
    (1 : ZMod M) hstep (by
      simp)

theorem singletonProductExponentSingleCycle
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
  letI : Fintype Terminal := Fintype.ofFinite Terminal
  productExponentSingleCycle terminalStep terminalRank
    (fun q : Terminal => if q = q0 then (1 : ZMod M) else 0)
    base hstep (by
      simp)

theorem complementSingletonProductExponentSingleCycle
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
  productExponentSingleCycle terminalStep terminalRank
    (fun q : Terminal => if q = q0 then (0 : ZMod M) else 1)
    base hstep hunit

theorem squareSubOneProductExponentSingleCycle
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
  productExponentSingleCycle terminalStep terminalRank exponent base hstep (by
    rw [hsum]
    exact squareSubOneUnitZModPow m k)

theorem complementSingletonSquareProductExponentSingleCycle
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
  squareSubOneProductExponentSingleCycle terminalStep terminalRank
    (fun q : Terminal => if q = q0 then (0 : ZMod (m ^ k)) else 1)
    base hstep (by
      rw [complementSingletonExponentSum (M := m ^ k) q0, hcard])

end UnitCarry

export UnitCarry
  (additiveSkewMap unitCarrySingleCycle rankUnitCarrySingleCycle
   pointCarry pointCarry_crossing pointCarry_of_ne pointCarrySum
   pointCarryUnit pointCarrySingleCycle
   singlePointCarry_eq_pointCarry negativeSinglePointCarry_eq_pointCarry
   singlePointCarrySingleCycle_pointCarry
   negativeSinglePointCarrySingleCycle_pointCarry
   singlePointCarrySum negativeSinglePointCarrySum
   singlePointCarryUnit negativeSinglePointCarryUnit
   singlePointCarrySingleCycle negativeSinglePointCarrySingleCycle
   squareSubOneCoprimeSelf squareSubOneCoprimePow
   squareSubOneUnitZModPow singletonExponentSum
   complementSingletonExponentSum
   productExponentMap productExponentSingleCycle
   pointProductExponentSingleCycle
   singletonPointProductExponentSingleCycle
   singletonProductExponentSingleCycle
   complementSingletonProductExponentSingleCycle
   squareSubOneProductExponentSingleCycle
   complementSingletonSquareProductExponentSingleCycle)

end EvenV11
