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

end Concrete

end RoundComposite
