import EvenV11.FinalTargetPhaseProductCertificateBridge

/-!
# Odd low-modulus closure (rewritten paper architecture)

New-architecture closure of the odd low-modulus range `m ≤ d` following the
rewritten manuscript (working tree
`/data/angel/repos/etc/even_modulus_rewrite_20260610/`,
`subtex/high_even_growth.tex` + `subtex/final_induction_framework.tex`):

* `cor:odd-chain-propagation` — modulus-free odd chain propagation: if
  `HED(D₀, m)` holds for some odd `D₀ ≥ 7`, then `HED(D, m)` holds for every
  odd `D ≥ D₀`; the growth propositions have no hidden hypothesis comparing
  `m` with the current dimension, so the iteration may cross the line `D = m`.
  With `D₀ = 7` and the dimension-7 finite certificates this closes
  `m ∈ {4, 6}` (`cor:special-low-modulus-chain-growth`).
* `cor:modulus-free-restart` — modulus-free restart of the high-even closure:
  for odd `d ≥ 7` and even `8 ≤ m ≤ d`, restart the high-even closure at
  `D₀ = m − 1` (an odd high-even pair since `m > D₀`) and grow past `D = m`.

Together these replace the endpoint-successor route of the earlier manuscript:
since `MarkedDimensionRange b m` forces even `4 ≤ m ≤ 2b + 1`, the odd child
dimension `d = 2b + 1 ≥ 9` always falls in `m ∈ {4, 6}` (chain propagation) or
`8 ≤ m ≤ d` (restart), so the old interface
`FinalOddEndpointPhaseProductTargetPromotion` is *derivable* — its parent
target and certificate inputs are simply not consumed.  The adapter
`oddEndpointPromotion_of_oddLowClosure` below is sorry-free, so the induction
spine and Main's checklist stay untouched.
-/

namespace EvenV11
namespace V28Hard
namespace OddLowClosureBridge

/-- New-architecture closure of the odd low-modulus range (rewritten paper:
`cor:odd-chain-propagation` + `cor:modulus-free-restart`).  Replaces the
retired endpoint-successor route. -/
structure OddLowClosure : Prop where
  /-- Chain propagation: `HED(7, m)` for `m ∈ {4, 6}` propagates up the odd
  dimensions (paper `cor:odd-chain-propagation`, instantiated at `D₀ = 7` as
  in `cor:special-low-modulus-chain-growth`; the chain fields are
  certificate-backed). -/
  chainPropagation :
    ∀ {d m : Nat}, 9 ≤ d → d % 2 = 1 → (m = 4 ∨ m = 6) →
      FinalMarkedTarget 7 m → FinalMarkedTarget d m
  /-- Modulus-free restart: for even `8 ≤ m ≤ d` (odd `d ≥ 9`), restart the
  high-even closure at `D₀ = m − 1` and grow past the `D = m` line (paper
  `cor:modulus-free-restart`).  Consumes the high-even promotion. -/
  modulusFreeRestart :
    FinalOddHighModulusTargetPromotion →
    ∀ {d m : Nat}, 9 ≤ d → d % 2 = 1 → Even m → 8 ≤ m → m ≤ d →
      FinalMarkedTarget d m

/-- The retired endpoint-successor interface is derivable from the
new-architecture closure: for `d = 2b + 1` with `4 ≤ b`,
`MarkedDimensionRange b m` forces even `4 ≤ m ≤ d`, so either `m ∈ {4, 6}`
(chain propagation from the closed dimension-7 finite witnesses) or
`8 ≤ m ≤ d` (modulus-free restart).  The parent target and the endpoint
certificate inputs are not needed.  Sorry-free. -/
theorem oddEndpointPromotion_of_oddLowClosure
    (closure : OddLowClosure)
    (high : FinalOddHighModulusTargetPromotion)
    (t74 : FinalMarkedTarget 7 4) (t76 : FinalMarkedTarget 7 6) :
    FinalOddEndpointPhaseProductTargetPromotion where
  oddEndpoint := fun {b m} hb hRange _parent _inputs => by
    obtain ⟨-, ⟨hm4, k, hk⟩, hmd⟩ := hRange
    have hd9 : 9 ≤ 2 * b + 1 := by omega
    have hodd : (2 * b + 1) % 2 = 1 := by omega
    rcases (by omega : m = 4 ∨ m = 6 ∨ 8 ≤ m) with h4 | h6 | h8
    · subst h4
      exact closure.chainPropagation hd9 hodd (Or.inl rfl) t74
    · subst h6
      exact closure.chainPropagation hd9 hodd (Or.inr rfl) t76
    · exact closure.modulusFreeRestart high hd9 hodd ⟨k, by omega⟩ h8 hmd

end OddLowClosureBridge
end V28Hard
end EvenV11
