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

theorem oddCoreHighModulusPrefixCount_of_goal
    (hHigh : OddCoreHighModulusPrefixCountGoal) :
    OddCoreHighModulusPrefixCount StandardCayleySolved := by
  intro d m hdodd hd5 _hm3 hmodd hdm
  exact hHigh hdodd hd5 hmodd hdm

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

end Concrete
end RoundComposite
