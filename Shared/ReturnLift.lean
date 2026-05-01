import Mathlib

namespace Shared

def IsSingleCycleMap {α : Type*} (f : α → α) : Prop :=
  Function.Bijective f ∧ ∀ x y : α, ∃ n : Nat, f^[n] x = y

theorem iterate_mul_base_of_periodic_return
    {α β : Type*} (S : α → α) (base : β → α) (R : β → β)
    (period : Nat)
    (hreturn : ∀ w : β, S^[period] (base w) = base (R w)) :
    ∀ n : Nat, ∀ w : β,
      S^[n * period] (base w) = base (R^[n] w) := by
  intro n
  induction n with
  | zero =>
      intro w
      simp
  | succ n ih =>
      intro w
      calc
        S^[(n + 1) * period] (base w)
            = S^[n * period + period] (base w) := by
                congr 1
                ring
        _ = S^[n * period] (S^[period] (base w)) := by
                rw [Function.iterate_add_apply]
        _ = S^[n * period] (base (R w)) := by
                rw [hreturn]
        _ = base (R^[n] (R w)) := ih (R w)
        _ = base (R^[n + 1] w) := by
                rw [Function.iterate_succ_apply]

theorem iterate_add_mul_base_of_periodic_return
    {α β : Type*} (S : α → α) (base : β → α) (R : β → β)
    (period : Nat)
    (hreturn : ∀ w : β, S^[period] (base w) = base (R w))
    (n r : Nat) (w : β) :
    S^[n * period + r] (base w) =
      S^[r] (base (R^[n] w)) := by
  calc
    S^[n * period + r] (base w)
        = S^[r] (S^[n * period] (base w)) := by
            simpa [Nat.add_comm] using
              Function.iterate_add_apply S r (n * period) (base w)
    _ = S^[r] (base (R^[n] w)) := by
            rw [iterate_mul_base_of_periodic_return S base R period hreturn n w]

theorem single_cycle_of_periodic_return_cover
    {α β : Type*} (S : α → α) (base : β → α) (R : β → β)
    (period : Nat)
    (hS : Function.Bijective S)
    (hreturn : ∀ w : β, S^[period] (base w) = base (R w))
    (hR : IsSingleCycleMap R)
    (hcover : ∀ x : α, ∃ w : β, ∃ k : Nat,
      k < period ∧ S^[k] (base w) = x) :
    IsSingleCycleMap S := by
  have hreturn_iter :
      ∀ n : Nat, ∀ w : β,
        S^[n * period] (base w) = base (R^[n] w) :=
    iterate_mul_base_of_periodic_return S base R period hreturn
  refine ⟨hS, ?_⟩
  intro x y
  rcases hcover x with ⟨a, r, hrlt, hx⟩
  rcases hcover y with ⟨b, s, _hslt, hy⟩
  by_cases hrs : r <= s
  · rcases hR.2 a b with ⟨q, hq⟩
    refine ⟨q * period + (s - r), ?_⟩
    rw [← hx, ← hy]
    calc
      S^[q * period + (s - r)] (S^[r] (base a))
          = S^[q * period + s] (base a) := by
              rw [← Function.iterate_add_apply]
              congr 1
              omega
      _ = S^[s + q * period] (base a) := by
              congr 1
              omega
      _ = S^[s] (S^[q * period] (base a)) := by
              rw [Function.iterate_add_apply]
      _ = S^[s] (base (R^[q] a)) := by
              rw [hreturn_iter]
      _ = S^[s] (base b) := by
              rw [hq]
  · rcases hR.2 (R a) b with ⟨q, hq⟩
    have hq' : R^[q + 1] a = b := by
      rw [Function.iterate_succ_apply]
      exact hq
    refine ⟨q * period + (period + s - r), ?_⟩
    rw [← hx, ← hy]
    calc
      S^[q * period + (period + s - r)] (S^[r] (base a))
          = S^[(q + 1) * period + s] (base a) := by
              rw [← Function.iterate_add_apply]
              congr 1
              calc
                q * period + (period + s - r) + r =
                    q * period + (period + s) := by
                  rw [Nat.add_assoc]
                  rw [Nat.sub_add_cancel]
                  omega
                _ = (q + 1) * period + s := by
                  ring
      _ = S^[s + (q + 1) * period] (base a) := by
              congr 1
              omega
      _ = S^[s] (S^[(q + 1) * period] (base a)) := by
              rw [Function.iterate_add_apply]
      _ = S^[s] (base (R^[q + 1] a)) := by
              rw [hreturn_iter]
      _ = S^[s] (base b) := by
              rw [hq']

end Shared
