import TorusD4.Lifts
import Mathlib.Tactic

namespace TorusD3Even

variable {α β : Type*}

theorem cycleOn_of_period_card [Fintype α] {F : α → α} {x : α}
    (hperiod : (F^[Fintype.card α]) x = x)
    (hminimal : ∀ n, 0 < n → n < Fintype.card α → (F^[n]) x ≠ x) :
    TorusD4.CycleOn (Fintype.card α) F x := by
  have hinj : Function.Injective (fun i : Fin (Fintype.card α) => (F^[i.1]) x) := by
    intro i j hij
    by_contra hne
    have hneVal : i.1 ≠ j.1 := by
      intro hval
      exact hne (Fin.ext hval)
    rcases lt_or_gt_of_ne hneVal with hijLt | hjiLt
    · have hkPos : 0 < i.1 + (Fintype.card α - j.1) := by
        omega
      have hkLt : i.1 + (Fintype.card α - j.1) < Fintype.card α := by
        omega
      have hreturn : (F^[i.1 + (Fintype.card α - j.1)]) x = x := by
        calc
          (F^[i.1 + (Fintype.card α - j.1)]) x
              = (F^[Fintype.card α - j.1]) ((F^[i.1]) x) := by
                  rw [Nat.add_comm, Function.iterate_add_apply]
          _ = (F^[Fintype.card α - j.1]) ((F^[j.1]) x) := by
                simpa using congrArg (F^[Fintype.card α - j.1]) hij
          _ = (F^[(Fintype.card α - j.1) + j.1]) x := by
                symm
                exact Function.iterate_add_apply F (Fintype.card α - j.1) j.1 x
          _ = (F^[Fintype.card α]) x := by
                rw [Nat.sub_add_cancel (Nat.le_of_lt j.2)]
          _ = x := hperiod
      exact hminimal _ hkPos hkLt hreturn
    · have hkPos : 0 < j.1 + (Fintype.card α - i.1) := by
        omega
      have hkLt : j.1 + (Fintype.card α - i.1) < Fintype.card α := by
        omega
      have hreturn : (F^[j.1 + (Fintype.card α - i.1)]) x = x := by
        calc
          (F^[j.1 + (Fintype.card α - i.1)]) x
              = (F^[Fintype.card α - i.1]) ((F^[j.1]) x) := by
                  rw [Nat.add_comm, Function.iterate_add_apply]
          _ = (F^[Fintype.card α - i.1]) ((F^[i.1]) x) := by
                symm
                simpa using congrArg (F^[Fintype.card α - i.1]) hij
          _ = (F^[(Fintype.card α - i.1) + i.1]) x := by
                symm
                exact Function.iterate_add_apply F (Fintype.card α - i.1) i.1 x
          _ = (F^[Fintype.card α]) x := by
                rw [Nat.sub_add_cancel (Nat.le_of_lt i.2)]
          _ = x := hperiod
      exact hminimal _ hkPos hkLt hreturn
  have hbij :
      Function.Bijective (fun i : Fin (Fintype.card α) => (F^[i.1]) x) := by
    exact (Fintype.bijective_iff_injective_and_card
      (fun i : Fin (Fintype.card α) => (F^[i.1]) x)).2 ⟨hinj, by simp⟩
  exact ⟨hbij, hperiod⟩

def blockTime (T : β → β) (rho : β → ℕ) (x0 : β) : ℕ → ℕ
  | 0 => 0
  | k + 1 => blockTime T rho x0 k + rho ((T^[k]) x0)

@[simp] theorem blockTime_zero (T : β → β) (rho : β → ℕ) (x0 : β) :
    blockTime T rho x0 0 = 0 := rfl

@[simp] theorem blockTime_succ (T : β → β) (rho : β → ℕ) (x0 : β) (k : ℕ) :
    blockTime T rho x0 (k + 1) = blockTime T rho x0 k + rho ((T^[k]) x0) := rfl

theorem iterate_blockTime {F : α → α} {embed : β → α} {T : β → β} {rho : β → ℕ} {x0 : β}
    (hreturn : ∀ x, (F^[rho x]) (embed x) = embed (T x)) :
    ∀ k, (F^[blockTime T rho x0 k]) (embed x0) = embed ((T^[k]) x0)
  | 0 => by simp [blockTime]
  | k + 1 => by
      calc
        (F^[blockTime T rho x0 (k + 1)]) (embed x0)
            = (F^[rho ((T^[k]) x0)]) ((F^[blockTime T rho x0 k]) (embed x0)) := by
                rw [blockTime, Nat.add_comm, Function.iterate_add_apply]
        _ = (F^[rho ((T^[k]) x0)]) (embed ((T^[k]) x0)) := by
              rw [iterate_blockTime (hreturn := hreturn) k]
        _ = embed (T ((T^[k]) x0)) := hreturn _
        _ = embed ((T^[k + 1]) x0) := by
              simp [Function.iterate_succ_apply']

theorem exists_blockTime_interval {T : β → β} {rho : β → ℕ} {x0 : β} :
    ∀ {M n : ℕ}, n < blockTime T rho x0 M →
      ∃ k, k < M ∧ blockTime T rho x0 k ≤ n ∧ n < blockTime T rho x0 (k + 1)
  | 0, n, h => by
      simp [blockTime] at h
  | M + 1, n, h => by
      by_cases hlt : n < blockTime T rho x0 M
      · rcases exists_blockTime_interval hlt with ⟨k, hkM, hkle, hklt⟩
        exact ⟨k, Nat.lt_trans hkM (Nat.lt_succ_self _), hkle, by simpa using hklt⟩
      · exact ⟨M, Nat.lt_succ_self _, Nat.le_of_not_gt hlt, by simpa [blockTime] using h⟩

theorem firstReturn_counting [Fintype α] {F : α → α} {embed : β → α}
    (hembed : Function.Injective embed)
    {T : β → β} {rho : β → ℕ} {M : ℕ} [Fact (0 < M)] {x0 : β}
    (hcycle : TorusD4.CycleOn M T x0)
    (hreturn : ∀ x, (F^[rho x]) (embed x) = embed (T x))
    (hfirst : ∀ x n, 0 < n → n < rho x → (F^[n]) (embed x) ∉ Set.range embed)
    (hsum : blockTime T rho x0 M = Fintype.card α) :
    TorusD4.CycleOn (Fintype.card α) F (embed x0) := by
  have hperiodTotal : (F^[blockTime T rho x0 M]) (embed x0) = embed x0 := by
    calc
      (F^[blockTime T rho x0 M]) (embed x0) = embed ((T^[M]) x0) := iterate_blockTime hreturn M
      _ = embed x0 := by rw [hcycle.2]
  have hminimalTotal :
      ∀ n, 0 < n → n < blockTime T rho x0 M → (F^[n]) (embed x0) ≠ embed x0 := by
    intro n hn0 hnLt hfix
    rcases exists_blockTime_interval (T := T) (rho := rho) (x0 := x0) hnLt with
      ⟨k, hkM, hkle, hklt⟩
    let r := n - blockTime T rho x0 k
    have hdecomp : n = blockTime T rho x0 k + r := by
      dsimp [r]
      omega
    have hklt' : n < blockTime T rho x0 k + rho ((T^[k]) x0) := by
      simpa [blockTime] using hklt
    have hrLt : r < rho ((T^[k]) x0) := by
      dsimp [r]
      omega
    have horbit : (F^[r]) (embed ((T^[k]) x0)) = embed x0 := by
      calc
        (F^[r]) (embed ((T^[k]) x0))
            = (F^[r]) ((F^[blockTime T rho x0 k]) (embed x0)) := by
                rw [iterate_blockTime (hreturn := hreturn) k]
        _ = (F^[r + blockTime T rho x0 k]) (embed x0) := by
              symm
              exact Function.iterate_add_apply F r (blockTime T rho x0 k) (embed x0)
        _ = (F^[n]) (embed x0) := by rw [Nat.add_comm, hdecomp]
        _ = embed x0 := hfix
    by_cases hr0 : r = 0
    · have hTk : (T^[k]) x0 = x0 := by
        apply hembed
        calc
          embed ((T^[k]) x0) = (F^[r]) (embed ((T^[k]) x0)) := by simp [hr0]
          _ = embed x0 := horbit
      have hk0 : 0 < k := by
        cases k with
        | zero =>
            simp [blockTime, hr0] at hdecomp
            omega
        | succ k =>
            exact Nat.succ_pos _
      have hkEq0 : k = 0 := by
        exact TorusD4.cycleOn_iterate_injective hcycle hkM Fact.out (by simpa using hTk)
      exact Nat.ne_of_gt hk0 hkEq0
    · have hr0' : 0 < r := Nat.pos_of_ne_zero hr0
      have hnot : (F^[r]) (embed ((T^[k]) x0)) ∉ Set.range embed :=
        hfirst _ r hr0' hrLt
      exact hnot ⟨x0, horbit.symm⟩
  have hperiodCard : (F^[Fintype.card α]) (embed x0) = embed x0 := by
    simpa [hsum] using hperiodTotal
  have hminimalCard :
      ∀ n, 0 < n → n < Fintype.card α → (F^[n]) (embed x0) ≠ embed x0 := by
    intro n hn0 hnLt
    apply hminimalTotal n hn0
    simpa [hsum] using hnLt
  exact cycleOn_of_period_card hperiodCard hminimalCard

end TorusD3Even
