import Mathlib
import RoundComposite.ActiveHall
import RoundComposite.PrefixCount
import RoundComposite.PrefixCountHalfSlack
import Shared.CayleyProduct

namespace RoundComposite

variable (Solved : Nat → Nat → Prop)

def UniformSolved (d : Nat) : Prop :=
  ∀ {m : Nat}, 3 ≤ m → Solved d m

def OddUniformSolved (d : Nat) : Prop :=
  ∀ {m : Nat}, 3 ≤ m → Odd m → Solved d m

theorem odd_uniform_of_uniform {d : Nat}
    (h : UniformSolved Solved d) :
    OddUniformSolved Solved d := by
  intro m hm _hodd
  exact h hm

def PointwiseCompositeExpansion : Prop :=
  ∀ {a b m : Nat}, 0 < a → 0 < b → 3 ≤ m →
    Solved a m → Solved b (m ^ a) → Solved (a * b) m

def OddPointwiseCompositeExpansion : Prop :=
  ∀ {a b m : Nat}, 0 < a → 0 < b → 3 ≤ m → Odd m →
    Solved a m → Solved b (m ^ a) → Solved (a * b) m

theorem odd_pointwise_of_pointwise
    (hExp : PointwiseCompositeExpansion Solved) :
    OddPointwiseCompositeExpansion Solved := by
  intro a b m ha hb hm _hodd hA hB
  exact hExp ha hb hm hA hB

theorem three_le_pow_of_three_le {m a : Nat} (hm : 3 ≤ m) (ha : 0 < a) :
    3 ≤ m ^ a := by
  exact le_trans hm (Nat.le_self_pow (Nat.ne_of_gt ha) m)

theorem uniform_mul_of_pointwise
    (hExp : PointwiseCompositeExpansion Solved)
    {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (hA : UniformSolved Solved a) (hB : UniformSolved Solved b) :
    UniformSolved Solved (a * b) := by
  intro m hm
  exact hExp ha hb hm (hA hm) (hB (three_le_pow_of_three_le hm ha))

def UniformMulClosed : Prop :=
  ∀ {a b : Nat}, 0 < a → 0 < b →
    UniformSolved Solved a → UniformSolved Solved b →
    UniformSolved Solved (a * b)

theorem uniform_mul_closed_of_pointwise
    (hExp : PointwiseCompositeExpansion Solved) :
    UniformMulClosed Solved := by
  intro a b ha hb hA hB
  exact uniform_mul_of_pointwise Solved hExp ha hb hA hB

theorem odd_uniform_mul_of_pointwise
    (hExp : OddPointwiseCompositeExpansion Solved)
    {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (hA : OddUniformSolved Solved a) (hB : OddUniformSolved Solved b) :
    OddUniformSolved Solved (a * b) := by
  intro m hm hodd
  exact hExp ha hb hm hodd (hA hm hodd)
    (hB (three_le_pow_of_three_le hm ha) hodd.pow)

def OddUniformMulClosed : Prop :=
  ∀ {a b : Nat}, 0 < a → 0 < b →
    OddUniformSolved Solved a → OddUniformSolved Solved b →
    OddUniformSolved Solved (a * b)

theorem odd_uniform_mul_closed_of_pointwise
    (hExp : OddPointwiseCompositeExpansion Solved) :
    OddUniformMulClosed Solved := by
  intro a b ha hb hA hB
  exact odd_uniform_mul_of_pointwise Solved hExp ha hb hA hB

def PrimeBaseSolved : Prop :=
  ∀ {p : Nat}, Nat.Prime p → UniformSolved Solved p

def OddPrimeBaseSolved : Prop :=
  ∀ {p : Nat}, Nat.Prime p → OddUniformSolved Solved p

theorem odd_prime_base_of_prime_base
    (hPrime : PrimeBaseSolved Solved) :
    OddPrimeBaseSolved Solved := by
  intro p hp
  exact odd_uniform_of_uniform Solved (hPrime hp)

theorem uniform_product_of_two_primes
    (hExp : PointwiseCompositeExpansion Solved)
    (hPrime : PrimeBaseSolved Solved)
    {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    UniformSolved Solved (p * q) := by
  exact uniform_mul_of_pointwise Solved hExp hp.pos hq.pos
    (hPrime hp) (hPrime hq)

theorem odd_uniform_product_of_two_primes
    (hExp : OddPointwiseCompositeExpansion Solved)
    (hPrime : OddPrimeBaseSolved Solved)
    {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    OddUniformSolved Solved (p * q) := by
  exact odd_uniform_mul_of_pointwise Solved hExp hp.pos hq.pos
    (hPrime hp) (hPrime hq)

theorem list_prod_pos_of_all_pos :
    ∀ {ds : List Nat}, (∀ d, d ∈ ds → 0 < d) → 0 < ds.prod
  | [], _ => by
      simp
  | d :: ds, hpos => by
      have hd : 0 < d := hpos d (by simp)
      have hds : 0 < ds.prod :=
        list_prod_pos_of_all_pos
          (fun e he => hpos e (by simp [he]))
      simpa using Nat.mul_pos hd hds

theorem uniform_prod_cons_of_pointwise
    (hExp : PointwiseCompositeExpansion Solved) :
    ∀ {d : Nat} {ds : List Nat},
      (∀ e, e ∈ d :: ds → 0 < e) →
      (∀ e, e ∈ d :: ds → UniformSolved Solved e) →
      UniformSolved Solved (d :: ds).prod
  | d, [], _hpos, hsol => by
      simpa using hsol d (by simp)
  | d, e :: es, hpos, hsol => by
      have hdpos : 0 < d := hpos d (by simp)
      have htailPos : ∀ x, x ∈ e :: es → 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      have htailSol : ∀ x, x ∈ e :: es → UniformSolved Solved x := by
        intro x hx
        exact hsol x (by simp [hx])
      have htail :
          UniformSolved Solved (e :: es).prod :=
        uniform_prod_cons_of_pointwise hExp htailPos htailSol
      have htailProdPos : 0 < (e :: es).prod :=
        list_prod_pos_of_all_pos htailPos
      simpa using
        uniform_mul_of_pointwise Solved hExp hdpos htailProdPos
          (hsol d (by simp)) htail

theorem uniform_product_of_prime_list
    (hExp : PointwiseCompositeExpansion Solved)
    (hPrime : PrimeBaseSolved Solved)
    {ps : List Nat} (hne : ps ≠ [])
    (hps : ∀ p, p ∈ ps → Nat.Prime p) :
    UniformSolved Solved ps.prod := by
  cases ps with
  | nil =>
      exact (hne rfl).elim
  | cons p ps =>
      exact uniform_prod_cons_of_pointwise Solved hExp
        (fun e he => (hps e he).pos)
        (fun e he => hPrime (hps e he))

theorem odd_uniform_prod_cons_of_pointwise
    (hExp : OddPointwiseCompositeExpansion Solved) :
    ∀ {d : Nat} {ds : List Nat},
      (∀ e, e ∈ d :: ds → 0 < e) →
      (∀ e, e ∈ d :: ds → OddUniformSolved Solved e) →
      OddUniformSolved Solved (d :: ds).prod
  | d, [], _hpos, hsol => by
      simpa using hsol d (by simp)
  | d, e :: es, hpos, hsol => by
      have hdpos : 0 < d := hpos d (by simp)
      have htailPos : ∀ x, x ∈ e :: es → 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      have htailSol : ∀ x, x ∈ e :: es → OddUniformSolved Solved x := by
        intro x hx
        exact hsol x (by simp [hx])
      have htail :
          OddUniformSolved Solved (e :: es).prod :=
        odd_uniform_prod_cons_of_pointwise hExp htailPos htailSol
      have htailProdPos : 0 < (e :: es).prod :=
        list_prod_pos_of_all_pos htailPos
      simpa using
        odd_uniform_mul_of_pointwise Solved hExp hdpos htailProdPos
          (hsol d (by simp)) htail

theorem odd_uniform_product_of_prime_list
    (hExp : OddPointwiseCompositeExpansion Solved)
    (hPrime : OddPrimeBaseSolved Solved)
    {ps : List Nat} (hne : ps ≠ [])
    (hps : ∀ p, p ∈ ps → Nat.Prime p) :
    OddUniformSolved Solved ps.prod := by
  cases ps with
  | nil =>
      exact (hne rfl).elim
  | cons p ps =>
      exact odd_uniform_prod_cons_of_pointwise Solved hExp
        (fun e he => (hps e he).pos)
        (fun e he => hPrime (hps e he))

def PrimeFactorList (d : Nat) : Prop :=
  ∃ ps : List Nat, ps ≠ [] ∧ ps.prod = d ∧
    ∀ p, p ∈ ps → Nat.Prime p

theorem uniform_of_prime_factor_list
    (hExp : PointwiseCompositeExpansion Solved)
    (hPrime : PrimeBaseSolved Solved)
    {d : Nat} (hfactor : PrimeFactorList d) :
    UniformSolved Solved d := by
  rcases hfactor with ⟨ps, hne, hprod, hps⟩
  rw [← hprod]
  exact uniform_product_of_prime_list Solved hExp hPrime hne hps

def PrimeFactorReduction : Prop :=
  ∀ {d : Nat}, PrimeFactorList d → UniformSolved Solved d

def OddPrimeFactorReduction : Prop :=
  ∀ {d : Nat}, PrimeFactorList d → OddUniformSolved Solved d

theorem prime_factor_reduction_of_pointwise
    (hExp : PointwiseCompositeExpansion Solved)
    (hPrime : PrimeBaseSolved Solved) :
    PrimeFactorReduction Solved := by
  intro d hfactor
  exact uniform_of_prime_factor_list Solved hExp hPrime hfactor

theorem odd_uniform_of_prime_factor_list
    (hExp : OddPointwiseCompositeExpansion Solved)
    (hPrime : OddPrimeBaseSolved Solved)
    {d : Nat} (hfactor : PrimeFactorList d) :
    OddUniformSolved Solved d := by
  rcases hfactor with ⟨ps, hne, hprod, hps⟩
  rw [← hprod]
  exact odd_uniform_product_of_prime_list Solved hExp hPrime hne hps

theorem odd_prime_factor_reduction_of_pointwise
    (hExp : OddPointwiseCompositeExpansion Solved)
    (hPrime : OddPrimeBaseSolved Solved) :
    OddPrimeFactorReduction Solved := by
  intro d hfactor
  exact odd_uniform_of_prime_factor_list Solved hExp hPrime hfactor

namespace Concrete

abbrev StandardTorusSolved : Nat → Nat → Prop :=
  Shared.TorusHamiltonDecomposition

abbrev StandardCayleySolved : Nat → Nat → Prop :=
  Shared.CayleyHamiltonDecomposition

abbrev StandardCoordinatizedCayleySolved : Nat → Nat → Prop :=
  Shared.CoordinatizedCayleyHamiltonDecomposition

variable (TorusSolved CayleySolved : Nat → Nat → Prop)

def TorusToCayley : Prop :=
  ∀ {d m : Nat}, 3 ≤ m → TorusSolved d m → CayleySolved d m

theorem uniform_cayley_of_uniform_torus
    (hTC : TorusToCayley TorusSolved CayleySolved)
    {d : Nat} (hTorus : UniformSolved TorusSolved d) :
    UniformSolved CayleySolved d := by
  intro m hm
  exact hTC hm (hTorus hm)

theorem odd_uniform_cayley_of_odd_uniform_torus
    (hTC : TorusToCayley TorusSolved CayleySolved)
    {d : Nat} (hTorus : OddUniformSolved TorusSolved d) :
    OddUniformSolved CayleySolved d := by
  intro m hm hodd
  exact hTC hm (hTorus hm hodd)

theorem cayley_prime_factor_reduction_of_torus_pointwise
    (hExp : PointwiseCompositeExpansion TorusSolved)
    (hPrime : PrimeBaseSolved TorusSolved)
    (hTC : TorusToCayley TorusSolved CayleySolved) :
    PrimeFactorReduction CayleySolved := by
  intro d hfactor
  exact uniform_cayley_of_uniform_torus TorusSolved CayleySolved hTC
    (prime_factor_reduction_of_pointwise TorusSolved hExp hPrime hfactor)

theorem cayley_prime_factor_reduction_of_cayley_pointwise
    (hExp : PointwiseCompositeExpansion CayleySolved)
    (hPrime : PrimeBaseSolved CayleySolved) :
    PrimeFactorReduction CayleySolved := by
  exact prime_factor_reduction_of_pointwise CayleySolved hExp hPrime

theorem cayley_odd_prime_factor_reduction_of_torus_pointwise
    (hExp : OddPointwiseCompositeExpansion TorusSolved)
    (hPrime : OddPrimeBaseSolved TorusSolved)
    (hTC : TorusToCayley TorusSolved CayleySolved) :
    OddPrimeFactorReduction CayleySolved := by
  intro d hfactor
  exact odd_uniform_cayley_of_odd_uniform_torus TorusSolved CayleySolved hTC
    (odd_prime_factor_reduction_of_pointwise TorusSolved hExp hPrime hfactor)

theorem cayley_odd_prime_factor_reduction_of_cayley_pointwise
    (hExp : OddPointwiseCompositeExpansion CayleySolved)
    (hPrime : OddPrimeBaseSolved CayleySolved) :
    OddPrimeFactorReduction CayleySolved := by
  exact odd_prime_factor_reduction_of_pointwise CayleySolved hExp hPrime

theorem standard_torus_to_cayley :
    TorusToCayley StandardTorusSolved StandardCayleySolved := by
  intro _d _m _hm h
  exact h

theorem standard_cayley_of_standard_coordinatized
    {d m : Nat}
    (h : StandardCoordinatizedCayleySolved d m) :
    StandardCayleySolved d m :=
  Shared.cayleyHamiltonDecomposition_of_coordinatized h

theorem standard_coordinatized_of_standard_cayley
    {d m : Nat} (hd : 0 < d) (hm : 3 ≤ m)
    (h : StandardCayleySolved d m) :
    StandardCoordinatizedCayleySolved d m := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have hpow3 : 3 ≤ m ^ d := three_le_pow_of_three_le hm hd
  have hpow1 : 1 < m ^ d := lt_of_lt_of_le (by decide : 1 < 3) hpow3
  letI : NeZero m := ⟨ne_of_gt hmpos⟩
  letI : NeZero (m ^ d) := ⟨ne_of_gt (lt_trans (by decide : 0 < 1) hpow1)⟩
  exact Shared.coordinatizedCayleyHamiltonDecomposition_of_single_cycle
    hpow1 h

theorem standard_cayley_product_of_left_coordinatized
    {a b m : Nat} (_ha : 0 < a) (_hb : 0 < b) (_hm : 3 ≤ m)
    (hA : StandardCoordinatizedCayleySolved a m)
    (hB : StandardCayleySolved b (m ^ a)) :
    StandardCayleySolved (a * b) m :=
  Shared.cayleyHamiltonDecomposition_product_of_left_coordinatized hA hB

theorem standard_cayley_product_of_standard_cayley
    {a b m : Nat} (ha : 0 < a) (hb : 0 < b) (hm : 3 ≤ m)
    (hA : StandardCayleySolved a m)
    (hB : StandardCayleySolved b (m ^ a)) :
    StandardCayleySolved (a * b) m :=
  standard_cayley_product_of_left_coordinatized ha hb hm
    (standard_coordinatized_of_standard_cayley ha hm hA)
    hB

theorem standard_cayley_pointwise_composite_expansion :
    PointwiseCompositeExpansion StandardCayleySolved := by
  intro a b m ha hb hm hA hB
  exact standard_cayley_product_of_standard_cayley ha hb hm hA hB

theorem standard_cayley_odd_pointwise_composite_expansion :
    OddPointwiseCompositeExpansion StandardCayleySolved := by
  exact odd_pointwise_of_pointwise StandardCayleySolved
    standard_cayley_pointwise_composite_expansion

theorem standard_torus_product_of_left_coordinatized
    {a b m : Nat} (ha : 0 < a) (hb : 0 < b) (hm : 3 ≤ m)
    (hA : StandardCoordinatizedCayleySolved a m)
    (hB : StandardTorusSolved b (m ^ a)) :
    StandardTorusSolved (a * b) m :=
  standard_cayley_product_of_left_coordinatized ha hb hm hA hB

theorem standard_torus_product_of_standard_torus
    {a b m : Nat} (ha : 0 < a) (hb : 0 < b) (hm : 3 ≤ m)
    (hA : StandardTorusSolved a m)
    (hB : StandardTorusSolved b (m ^ a)) :
    StandardTorusSolved (a * b) m :=
  standard_cayley_product_of_standard_cayley ha hb hm hA hB

theorem standard_torus_pointwise_composite_expansion :
    PointwiseCompositeExpansion StandardTorusSolved := by
  intro a b m ha hb hm hA hB
  exact standard_torus_product_of_standard_torus ha hb hm hA hB

theorem standard_torus_odd_pointwise_composite_expansion :
    OddPointwiseCompositeExpansion StandardTorusSolved := by
  exact odd_pointwise_of_pointwise StandardTorusSolved
    standard_torus_pointwise_composite_expansion

theorem odd_uniform_cayley_mul_of_left_coordinatized
    {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (hA : OddUniformSolved StandardCoordinatizedCayleySolved a)
    (hB : OddUniformSolved StandardCayleySolved b) :
    OddUniformSolved StandardCayleySolved (a * b) := by
  intro m hm hodd
  exact standard_cayley_product_of_left_coordinatized ha hb hm
    (hA hm hodd)
    (hB (three_le_pow_of_three_le hm ha) hodd.pow)

theorem odd_uniform_cayley_mul_of_standard
    {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (hA : OddUniformSolved StandardCayleySolved a)
    (hB : OddUniformSolved StandardCayleySolved b) :
    OddUniformSolved StandardCayleySolved (a * b) := by
  intro m hm hodd
  exact standard_cayley_product_of_standard_cayley ha hb hm
    (hA hm hodd)
    (hB (three_le_pow_of_three_le hm ha) hodd.pow)

theorem odd_uniform_standard_cayley_prod_cons_of_product :
    ∀ {d : Nat} {ds : List Nat},
      (∀ e, e ∈ d :: ds → 0 < e) →
      (∀ e, e ∈ d :: ds → OddUniformSolved StandardCayleySolved e) →
      OddUniformSolved StandardCayleySolved (d :: ds).prod
  | d, [], _hpos, hsol => by
      simpa using hsol d (by simp)
  | d, e :: es, hpos, hsol => by
      have hdpos : 0 < d := hpos d (by simp)
      have htailPos : ∀ x, x ∈ e :: es → 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      have htailSol :
          ∀ x, x ∈ e :: es → OddUniformSolved StandardCayleySolved x := by
        intro x hx
        exact hsol x (by simp [hx])
      have htail :
          OddUniformSolved StandardCayleySolved (e :: es).prod :=
        odd_uniform_standard_cayley_prod_cons_of_product
          htailPos htailSol
      have htailProdPos : 0 < (e :: es).prod :=
        list_prod_pos_of_all_pos htailPos
      simpa using
        odd_uniform_cayley_mul_of_standard hdpos htailProdPos
          (hsol d (by simp)) htail

theorem standard_cayley_prime_factor_reduction_of_torus_pointwise
    (hExp : PointwiseCompositeExpansion StandardTorusSolved)
    (hPrime : PrimeBaseSolved StandardTorusSolved) :
    PrimeFactorReduction StandardCayleySolved := by
  exact cayley_prime_factor_reduction_of_torus_pointwise
    StandardTorusSolved StandardCayleySolved hExp hPrime standard_torus_to_cayley

theorem standard_cayley_odd_prime_factor_reduction_of_torus_pointwise
    (hExp : OddPointwiseCompositeExpansion StandardTorusSolved)
    (hPrime : OddPrimeBaseSolved StandardTorusSolved) :
    OddPrimeFactorReduction StandardCayleySolved := by
  exact cayley_odd_prime_factor_reduction_of_torus_pointwise
    StandardTorusSolved StandardCayleySolved hExp hPrime standard_torus_to_cayley

end Concrete

end RoundComposite
