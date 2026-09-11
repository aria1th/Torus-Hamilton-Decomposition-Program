-- STATUS: main-path
import TorusEven.Entry.Seed.Entry
import TorusEven.Goals

namespace TorusEven

theorem even_odd_degree : EvenOddDegreeGoal := by
  intro d m hd hd7 hm
  haveI : NeZero m := ⟨by have := hm.2; omega⟩
  obtain ⟨k, hk⟩ := hd
  have hp : 2 ≤ k - 1 := by omega
  have he : d = 2 * (k - 1) + 3 := by omega
  rw [he]
  exact Entry.Seed.hamilton_decomposition (k - 1) hp hm.2 hm.1

theorem d7_even : D7EvenGoal := fun hm hm4 => even_odd_degree (by decide) (by decide) ⟨hm, hm4⟩

theorem even_successor : EvenSuccessorGoal := by
  intro b m hb hm _
  exact even_odd_degree ⟨b, by omega⟩ (by omega) hm

end TorusEven
