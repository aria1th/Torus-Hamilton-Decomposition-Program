import RoundComposite.ConcreteEndpoints

namespace RoundComposite

inductive SolvedBySeedSemigroup : Nat → Prop
  | two : SolvedBySeedSemigroup 2
  | three : SolvedBySeedSemigroup 3
  | mul {a b : Nat} :
      SolvedBySeedSemigroup a →
      SolvedBySeedSemigroup b →
      SolvedBySeedSemigroup (a * b)

namespace SolvedBySeedSemigroup

theorem pos : ∀ {b : Nat}, SolvedBySeedSemigroup b → 0 < b
  | _, two => by decide
  | _, three => by decide
  | _, mul ha hb => Nat.mul_pos (pos ha) (pos hb)

theorem three_mul_two_pow :
    ∀ n : Nat, SolvedBySeedSemigroup (3 * 2 ^ n)
  | 0 => by
      simpa using three
  | n + 1 => by
      have h := mul (three_mul_two_pow n) two
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem four_mul_two_pow :
    ∀ n : Nat, SolvedBySeedSemigroup (4 * 2 ^ n)
  | 0 => by
      have h := mul two two
      norm_num at h ⊢
      exact h
  | n + 1 => by
      have h := mul (four_mul_two_pow n) two
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem oddUniformSolved
    {Solved : Nat → Nat → Prop}
    (hMul : OddUniformMulClosed Solved)
    (h2 : OddUniformSolved Solved 2)
    (h3 : OddUniformSolved Solved 3) :
    ∀ {b : Nat}, SolvedBySeedSemigroup b → OddUniformSolved Solved b
  | _, two => h2
  | _, three => h3
  | _, mul ha hb =>
      hMul (pos ha) (pos hb)
        (oddUniformSolved hMul h2 h3 ha)
        (oddUniformSolved hMul h2 h3 hb)

end SolvedBySeedSemigroup

def twoThreeBlockParts (b d : Nat) : List Nat :=
  let r := d - 2 * b
  List.replicate r 3 ++ List.replicate (b - r) 2

theorem twoThreeBlockParts_spec {b d : Nat}
    (h : 2 * b < d ∧ d ≤ 3 * b) :
    (twoThreeBlockParts b d).length = b ∧
    (twoThreeBlockParts b d).sum = d ∧
    ∀ k, k ∈ twoThreeBlockParts b d → k = 2 ∨ k = 3 := by
  let r := d - 2 * b
  have hrb : r ≤ b := by omega
  have hd : d = 2 * b + r := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [twoThreeBlockParts]
    omega
  · simp [twoThreeBlockParts, List.sum_replicate]
    omega
  · intro k hk
    simp [twoThreeBlockParts] at hk
    rcases hk with hk | hk
    · exact Or.inr hk.2
    · exact Or.inl hk.2

theorem twoThreeBlockParts_tail_gt_base {b d : Nat}
    (h : 2 * b < d ∧ d ≤ 3 * b) :
    b < d - b := by
  omega

theorem twoThreeBlockParts_tail_le_two_base {b d : Nat}
    (h : 2 * b < d ∧ d ≤ 3 * b) :
    d - b ≤ 2 * b := by
  omega

def unitCarryPacket (m k : Nat) : List Nat :=
  if k = 2 then
    [1, m - 1]
  else if k = 3 then
    [1, 1, m - 2]
  else
    []

theorem coprime_m_sub_one {m : Nat} (hm1 : 1 ≤ m) :
    Nat.Coprime (m - 1) m := by
  exact (Nat.coprime_self_sub_left hm1).2 (by simp)

theorem odd_coprime_m_sub_two {m : Nat} (hm2 : 2 ≤ m) (hodd : Odd m) :
    Nat.Coprime (m - 2) m := by
  exact (Nat.coprime_self_sub_left hm2).2 hodd.coprime_two_left

theorem unitCarryPacket_spec {m k : Nat}
    (hm3 : 3 ≤ m) (hodd : Odd m) (hk : k = 2 ∨ k = 3) :
    (unitCarryPacket m k).length = k ∧
    (unitCarryPacket m k).sum = m ∧
    ∀ a, a ∈ unitCarryPacket m k → 0 < a ∧ a < m ∧ Nat.Coprime a m := by
  rcases hk with rfl | rfl
  · have hcop1 : Nat.Coprime 1 m := by simp
    have hcopm1 : Nat.Coprime (m - 1) m :=
      coprime_m_sub_one (by omega)
    refine ⟨by simp [unitCarryPacket], ?_, ?_⟩
    · simp [unitCarryPacket]
      omega
    · intro a ha
      simp [unitCarryPacket] at ha
      rcases ha with rfl | ha
      · exact ⟨by omega, by omega, hcop1⟩
      · rcases ha with rfl
        · exact ⟨by omega, by omega, hcopm1⟩
  · have hcop1 : Nat.Coprime 1 m := by simp
    have hcopm2 : Nat.Coprime (m - 2) m :=
      odd_coprime_m_sub_two (by omega) hodd
    refine ⟨by simp [unitCarryPacket], ?_, ?_⟩
    · simp [unitCarryPacket]
      omega
    · intro a ha
      simp [unitCarryPacket] at ha
      rcases ha with rfl | ha
      · exact ⟨by omega, by omega, hcop1⟩
      · rcases ha with rfl
        · exact ⟨by omega, by omega, hcopm2⟩

theorem twoThreeBlockParts_unitCarryPacket_spec {b d m k : Nat}
    (hm3 : 3 ≤ m) (hodd : Odd m)
    (hbd : 2 * b < d ∧ d ≤ 3 * b)
    (hk : k ∈ twoThreeBlockParts b d) :
    (unitCarryPacket m k).length = k ∧
    (unitCarryPacket m k).sum = m ∧
    ∀ a, a ∈ unitCarryPacket m k → 0 < a ∧ a < m ∧ Nat.Coprime a m := by
  exact unitCarryPacket_spec hm3 hodd ((twoThreeBlockParts_spec hbd).2.2 k hk)

def unitCarryPackets (m b d : Nat) : List (List Nat) :=
  (twoThreeBlockParts b d).map (unitCarryPacket m)

theorem unitCarryPacketsForBlocks_spec {m : Nat}
    (hm3 : 3 ≤ m) (hodd : Odd m) :
    ∀ ks : List Nat,
      (∀ k, k ∈ ks → k = 2 ∨ k = 3) →
      ((ks.map (unitCarryPacket m)).map List.length).sum = ks.sum ∧
      ∀ packet, packet ∈ ks.map (unitCarryPacket m) →
        packet.sum = m ∧
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m
  | [], _ => by
      simp
  | k :: ks, hks => by
      have hk : k = 2 ∨ k = 3 := hks k (by simp)
      have htail : ∀ j, j ∈ ks → j = 2 ∨ j = 3 := by
        intro j hj
        exact hks j (by simp [hj])
      have hpacket := unitCarryPacket_spec hm3 hodd hk
      have ih := unitCarryPacketsForBlocks_spec hm3 hodd ks htail
      refine ⟨?_, ?_⟩
      · simp [hpacket.1]
        simpa [List.map_map, Function.comp_def] using ih.1
      · intro packet hpacketMem
        rcases List.mem_map.mp hpacketMem with ⟨j, hj, rfl⟩
        exact (unitCarryPacket_spec hm3 hodd (hks j (by simp [hj]))).2

theorem unitCarryPackets_spec {b d m : Nat}
    (hm3 : 3 ≤ m) (hodd : Odd m)
    (hbd : 2 * b < d ∧ d ≤ 3 * b) :
    (unitCarryPackets m b d).length = b ∧
    ((unitCarryPackets m b d).map List.length).sum = d ∧
    ∀ packet, packet ∈ unitCarryPackets m b d →
      packet.sum = m ∧
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m := by
  have hparts := twoThreeBlockParts_spec hbd
  have hpackets :=
    unitCarryPacketsForBlocks_spec hm3 hodd (twoThreeBlockParts b d) hparts.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [unitCarryPackets] using hparts.1
  · exact hpackets.1.trans hparts.2.1
  · simpa [unitCarryPackets] using hpackets.2

structure SmallBaseUnitPacketWitness (d m : Nat) where
  b : Nat
  seed : SolvedBySeedSemigroup b
  range : 2 * b < d ∧ d ≤ 3 * b
  packets : List (List Nat)
  packets_length : packets.length = b
  packets_total_length : (packets.map List.length).sum = d
  packet_sum : ∀ packet, packet ∈ packets → packet.sum = m
  packet_units :
    ∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m

namespace Concrete

theorem standard_cayley_odd_uniform_of_seed_semigroup
    {b : Nat} (hb : SolvedBySeedSemigroup b) :
    OddUniformSolved StandardCayleySolved b :=
  SolvedBySeedSemigroup.oddUniformSolved
    (Solved := StandardCayleySolved)
    (odd_uniform_mul_closed_of_pointwise
      StandardCayleySolved standard_cayley_odd_pointwise_composite_expansion)
    standard_cayley_odd_uniform_2
    standard_cayley_odd_uniform_3
    hb

theorem seed_semigroup_base_available
    {d : Nat} (_hdodd : Odd d) (hd13 : 13 ≤ d) :
    ∃ b : Nat,
      SolvedBySeedSemigroup b ∧
      2 * b < d ∧ d ≤ 3 * b := by
  let q := (d - 1) / 6
  let n := Nat.log 2 q
  let p := 2 ^ n
  have hq2 : 2 ≤ q := by
    have h12 : 2 * 6 ≤ d - 1 := by omega
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 6)).2 h12
  have hqne : q ≠ 0 := by omega
  have hp_le_q : p ≤ q := by
    simpa [p, n] using Nat.pow_log_le_self 2 hqne
  have hq_lt_2p : q < 2 * p := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q
    simpa [p, n, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hq_floor : q * 6 ≤ d - 1 := by
    simpa [q] using Nat.div_mul_le_self (d - 1) 6
  have h6p_le : 6 * p ≤ d - 1 := by
    have hmul : p * 6 ≤ q * 6 := Nat.mul_le_mul_right 6 hp_le_q
    omega
  have h6p_lt : 6 * p < d := by omega
  have hdsub_lt : d - 1 < (q + 1) * 6 := by
    simpa [q] using
      Nat.lt_mul_of_div_lt (Nat.lt_succ_self q) (by decide : 0 < 6)
  have hd_le_6q1 : d ≤ (q + 1) * 6 := by omega
  have hq1_le : q + 1 ≤ 2 * p := Nat.succ_le_of_lt hq_lt_2p
  have hupper : d ≤ 12 * p := by
    have hmul : (q + 1) * 6 ≤ (2 * p) * 6 :=
      Nat.mul_le_mul_right 6 hq1_le
    omega
  by_cases hlow : d ≤ 9 * p
  · refine ⟨3 * p, ?_, ?_, ?_⟩
    · simpa [p, n] using SolvedBySeedSemigroup.three_mul_two_pow n
    · omega
    · omega
  · have h9lt : 9 * p < d := lt_of_not_ge hlow
    refine ⟨4 * p, ?_, ?_, ?_⟩
    · simpa [p, n] using SolvedBySeedSemigroup.four_mul_two_pow n
    · omega
    · omega

noncomputable def smallBaseUnitPacketWitness
    {d m : Nat} (hdodd : Odd d) (hd13 : 13 ≤ d)
    (hm3 : 3 ≤ m) (hmodd : Odd m) :
    SmallBaseUnitPacketWitness d m := by
  let ex := seed_semigroup_base_available hdodd hd13
  let b := Classical.choose ex
  have hbSpec :
      SolvedBySeedSemigroup b ∧ 2 * b < d ∧ d ≤ 3 * b :=
    Classical.choose_spec ex
  let hbSeed := hbSpec.1
  let hbRange := hbSpec.2
  have hpackets := unitCarryPackets_spec hm3 hmodd hbRange
  exact {
    b := b
    seed := hbSeed
    range := hbRange
    packets := unitCarryPackets m b d
    packets_length := hpackets.1
    packets_total_length := hpackets.2.1
    packet_sum := fun packet hp => (hpackets.2.2 packet hp).1
    packet_units := fun packet hp a ha => (hpackets.2.2 packet hp).2 a ha
  }

theorem smallBaseUnitPacketWitness_solvedBase
    {d m : Nat} (w : SmallBaseUnitPacketWitness d m) :
    OddUniformSolved StandardCayleySolved w.b :=
  standard_cayley_odd_uniform_of_seed_semigroup w.seed

end Concrete

end RoundComposite
