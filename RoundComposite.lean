import Mathlib

namespace RoundComposite

variable (Solved : Nat → Nat → Prop)

def UniformSolved (d : Nat) : Prop :=
  ∀ {m : Nat}, 3 ≤ m → Solved d m

def PointwiseCompositeExpansion : Prop :=
  ∀ {a b m : Nat}, 0 < a → 0 < b → 3 ≤ m →
    Solved a m → Solved b (m ^ a) → Solved (a * b) m

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

def PrimeBaseSolved : Prop :=
  ∀ {p : Nat}, Nat.Prime p → UniformSolved Solved p

theorem uniform_product_of_two_primes
    (hExp : PointwiseCompositeExpansion Solved)
    (hPrime : PrimeBaseSolved Solved)
    {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    UniformSolved Solved (p * q) := by
  exact uniform_mul_of_pointwise Solved hExp hp.pos hq.pos
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

theorem prime_factor_reduction_of_pointwise
    (hExp : PointwiseCompositeExpansion Solved)
    (hPrime : PrimeBaseSolved Solved) :
    PrimeFactorReduction Solved := by
  intro d hfactor
  exact uniform_of_prime_factor_list Solved hExp hPrime hfactor

namespace Concrete

variable (TorusSolved CayleySolved : Nat → Nat → Prop)

def TorusToCayley : Prop :=
  ∀ {d m : Nat}, 3 ≤ m → TorusSolved d m → CayleySolved d m

theorem uniform_cayley_of_uniform_torus
    (hTC : TorusToCayley TorusSolved CayleySolved)
    {d : Nat} (hTorus : UniformSolved TorusSolved d) :
    UniformSolved CayleySolved d := by
  intro m hm
  exact hTC hm (hTorus hm)

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

end Concrete

end RoundComposite
