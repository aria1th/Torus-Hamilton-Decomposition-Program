import TorusD3Odd.Cycles
import TorusD4.Lifts
import Mathlib.Tactic

namespace TorusD3Odd

def KMap : Color → FullCoord m → FullCoord m
  | 0, ((i, k), s) => ((i + 1, k), s + 1)
  | 1, (u, s) => (u, s + 1)
  | 2, ((i, k), s) => ((i, k + 1), s + 1)

@[simp] theorem KMap_snd (c : Color) (z : FullCoord m) :
    (KMap (m := m) c z).2 = z.2 + 1 := by
  rcases z with ⟨u, s⟩
  rcases u with ⟨i, k⟩
  fin_cases c <;> rfl

@[simp] theorem coordOfPoint_bump (c : Color) (x : Point m) :
    coordOfPoint (m := m) (bump x c) = KMap (m := m) c (coordOfPoint (m := m) x) := by
  fin_cases c
  all_goals
    ext <;> simp [coordOfPoint, KMap, S, bump]
    all_goals ring_nf

@[simp] theorem splitPointEquiv_bump (c : Color) (x : Point m) :
    splitPointEquiv (m := m) (bump x c) = KMap (m := m) c (splitPointEquiv (m := m) x) := by
  simpa [splitPointEquiv] using coordOfPoint_bump (m := m) c x

theorem point_eq_phiLayer_of_splitPointEquiv_eq {x : Point m} {u : P0Coord m} {s : ZMod m}
    (h : splitPointEquiv (m := m) x = (u, s)) :
    x = phiLayer (m := m) u s := by
  apply (splitPointEquiv (m := m)).injective
  calc
    splitPointEquiv (m := m) x = (u, s) := h
    _ = splitPointEquiv (m := m) (phiLayer (m := m) u s) := by
          symm
          exact coordOfPoint_phiLayer (m := m) u s

theorem iterate_two_of_steps {α : Type*} {f : α → α} {x x1 x2 : α}
    (h1 : f x = x1) (h2 : f x1 = x2) :
    (f^[2]) x = x2 := by
  calc
    (f^[2]) x = f (f x) := by
      simp [Function.iterate_succ_apply']
    _ = f x1 := by rw [h1]
    _ = x2 := h2

theorem natCast_ne_zero_of_pos_lt [Fact (0 < m)] {n : ℕ} (hn0 : 0 < n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 0 := by
  intro h
  have h' : n % m = 0 % m := (ZMod.natCast_eq_natCast_iff' n 0 m).1 (by simpa using h)
  rw [Nat.mod_eq_of_lt hnm, Nat.zero_mod] at h'
  exact Nat.ne_of_gt hn0 h'

theorem natCast_ne_one_of_two_le_lt [Fact (1 < m)] {n : ℕ} (hn1 : 2 ≤ n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 1 := by
  intro h
  have h1m : 1 < m := Fact.out
  have h' : n % m = 1 % m := (ZMod.natCast_eq_natCast_iff' n 1 m).1 (by simpa using h)
  rw [Nat.mod_eq_of_lt hnm, Nat.mod_eq_of_lt h1m] at h'
  omega

theorem natCast_sub_two [Fact (0 < m)] (hm : 2 ≤ m) :
    ((m - 2 : ℕ) : ZMod m) = (-2 : ZMod m) := by
  calc
    ((m - 2 : ℕ) : ZMod m) = ((m : ZMod m) - ((2 : ℕ) : ZMod m)) := by
      rw [Nat.cast_sub hm]
    _ = (-2 : ZMod m) := by simp

@[simp] theorem zmod_zero_add_one : (0 : ZMod m) + 1 = 1 := by
  norm_num

@[simp] theorem zmod_one_add_one : (1 : ZMod m) + 1 = 2 := by
  norm_num

theorem one_ne_zero [Fact (2 < m)] : (1 : ZMod m) ≠ 0 := by
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) Fact.out⟩
  simpa using
    natCast_ne_zero_of_pos_lt (m := m) (n := 1) (by decide) (lt_trans (by decide : 1 < 2) Fact.out)

def pairColorMap (c : Color) : FullCoord m → FullCoord m :=
  fun z => splitPointEquiv (m := m) (colorMap (m := m) c ((splitPointEquiv (m := m)).symm z))

theorem splitPointEquiv_semiconj_pairColorMap (c : Color) :
    Function.Semiconj (splitPointEquiv (m := m)) (colorMap (m := m) c) (pairColorMap (m := m) c) := by
  intro x
  simp [pairColorMap]

theorem splitPointEquiv_symm_semiconj_colorMap (c : Color) :
    Function.Semiconj (splitPointEquiv (m := m)).symm (pairColorMap (m := m) c) (colorMap (m := m) c) := by
  exact (splitPointEquiv_semiconj_pairColorMap (m := m) c).inverse_left
    (splitPointEquiv (m := m)).left_inv (splitPointEquiv (m := m)).right_inv

@[simp] theorem pairColorMap_snd (c : Color) (z : FullCoord m) :
    (pairColorMap (m := m) c z).2 = z.2 + 1 := by
  rcases z with ⟨u, s⟩
  simpa [pairColorMap, coordOfPoint] using S_colorMap (m := m) c (phiLayer (m := m) u s)

@[simp] theorem pairColorMap_iterate_snd (c : Color) (n : ℕ) (z : FullCoord m) :
    (((pairColorMap (m := m) c)^[n]) z).2 = z.2 + n := by
  exact TorusD4.snd_iterate_add_one (m := m) (F := pairColorMap (m := m) c)
    (hstep := pairColorMap_snd (m := m) c) n z

theorem pairColorMap_eq_KMap_of_step (c d : Color) (u : P0Coord m) (s : ZMod m)
    (h : colorMap (m := m) c (phiLayer (m := m) u s) = bump (phiLayer (m := m) u s) d) :
    pairColorMap (m := m) c (u, s) = KMap (m := m) d (u, s) := by
  calc
    pairColorMap (m := m) c (u, s)
        = splitPointEquiv (m := m) (colorMap (m := m) c (phiLayer (m := m) u s)) := by
            rfl
    _ = splitPointEquiv (m := m) (bump (phiLayer (m := m) u s) d) := by rw [h]
    _ = KMap (m := m) d (splitPointEquiv (m := m) (phiLayer (m := m) u s)) := by
          rw [splitPointEquiv_bump]
    _ = KMap (m := m) d (u, s) := by simp

theorem pairColorMap_canonical (c : Color) (u : P0Coord m) (s : ZMod m)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    pairColorMap (m := m) c (u, s) = KMap (m := m) c (u, s) := by
  have hlow : ¬ (s = 0 ∨ s = 1) := by
    intro hs
    rcases hs with hs | hs
    · exact hs0 hs
    · exact hs1 hs
  apply pairColorMap_eq_KMap_of_step (m := m) c c u s
  fin_cases c
  · simp [colorMap, f0, hs0, hs1]
  · simp [colorMap, f1, hs0, hs1]
  · simp [colorMap, f2, hs0, hs1]

theorem iterate_K0 (n : ℕ) (i k s : ZMod m) :
    ((KMap (m := m) 0)^[n]) ((i, k), s) = ((i + n, k), s + n) := by
  induction n generalizing i k s with
  | zero =>
      simp [KMap]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [KMap, Nat.cast_add]
      all_goals ring

theorem iterate_K1 (n : ℕ) (u : P0Coord m) (s : ZMod m) :
    ((KMap (m := m) 1)^[n]) (u, s) = (u, s + n) := by
  induction n generalizing u s with
  | zero =>
      simp [KMap]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [KMap, Nat.cast_add]
      ring

theorem iterate_K2 (n : ℕ) (i k s : ZMod m) :
    ((KMap (m := m) 2)^[n]) ((i, k), s) = ((i, k + n), s + n) := by
  induction n generalizing i k s with
  | zero =>
      simp [KMap]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [KMap, Nat.cast_add]
      all_goals ring

theorem iterate_pairColorMap_from_two_eq_iterate_KMap [Fact (2 < m)] (c : Color) :
    ∀ n u, n ≤ m - 2 →
      ((pairColorMap (m := m) c)^[n]) (u, (2 : ZMod m)) =
        ((KMap (m := m) c)^[n]) (u, (2 : ZMod m))
  | 0, u, _ => by simp
  | n + 1, u, hn => by
      have hm2 : 2 < m := Fact.out
      letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) hm2⟩
      letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) hm2⟩
      have hlt : n < m - 2 := Nat.lt_of_succ_le hn
      have hcur_lt : 2 + n < m := by omega
      have hs0 : (((2 + n : ℕ) : ZMod m)) ≠ 0 := by
        exact natCast_ne_zero_of_pos_lt (m := m) (by omega) hcur_lt
      have hs1 : (((2 + n : ℕ) : ZMod m)) ≠ 1 := by
        exact natCast_ne_one_of_two_le_lt (m := m) (by omega) hcur_lt
      have hs0z : (2 : ZMod m) + n ≠ 0 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hs0
      have hs1z : (2 : ZMod m) + n ≠ 1 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hs1
      have hsnd :
          ((((KMap (m := m) c)^[n]) (u, (2 : ZMod m))).2) = (2 : ZMod m) + n := by
        exact TorusD4.snd_iterate_add_one (m := m) (F := KMap (m := m) c)
          (hstep := KMap_snd (m := m) c) n (u, (2 : ZMod m))
      have hs0' : (((KMap (m := m) c)^[n]) (u, (2 : ZMod m))).2 ≠ 0 := by
        rw [hsnd]
        exact hs0z
      have hs1' : (((KMap (m := m) c)^[n]) (u, (2 : ZMod m))).2 ≠ 1 := by
        rw [hsnd]
        exact hs1z
      calc
        ((pairColorMap (m := m) c)^[n + 1]) (u, (2 : ZMod m))
            = pairColorMap (m := m) c (((pairColorMap (m := m) c)^[n]) (u, (2 : ZMod m))) := by
                rw [Function.iterate_succ_apply']
        _ = pairColorMap (m := m) c (((KMap (m := m) c)^[n]) (u, (2 : ZMod m))) := by
              rw [iterate_pairColorMap_from_two_eq_iterate_KMap (m := m) c n u (Nat.le_of_lt hlt)]
        _ = KMap (m := m) c (((KMap (m := m) c)^[n]) (u, (2 : ZMod m))) := by
              simpa using
                pairColorMap_canonical (m := m) c
                  (((KMap (m := m) c)^[n]) (u, (2 : ZMod m))).1
                  (((KMap (m := m) c)^[n]) (u, (2 : ZMod m))).2
                  hs0' hs1'
        _ = ((KMap (m := m) c)^[n + 1]) (u, (2 : ZMod m)) := by
              symm
              rw [Function.iterate_succ_apply']

theorem pairColorMap0_two [Fact (2 < m)] (u : P0Coord m) :
    ((pairColorMap (m := m) 0)^[2]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (2 : ZMod m)
        (u.1 + TorusD4.delta m (u.2 = 0), u.2 + 1) := by
  rcases u with ⟨i, k⟩
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  by_cases hk0 : k = 0
  · have h1 :
        pairColorMap (m := m) 0 (((i, k), (0 : ZMod m))) = KMap (m := m) 0 (((i, k), (0 : ZMod m))) := by
          apply pairColorMap_eq_KMap_of_step (m := m) 0 0 (i, k) 0
          simp [colorMap, f0, hk0]
    have h2' :
        pairColorMap (m := m) 0 (((i + 1, k), (1 : ZMod m))) =
          KMap (m := m) 2 (((i + 1, k), (1 : ZMod m))) := by
            apply pairColorMap_eq_KMap_of_step (m := m) 0 2 (i + 1, k) 1
            simp [colorMap, f0, h10]
    have h2 :
        pairColorMap (m := m) 0 (KMap (m := m) 0 (((i, k), (0 : ZMod m)))) =
          KMap (m := m) 2 (KMap (m := m) 0 (((i, k), (0 : ZMod m)))) := by
            simpa [KMap] using h2'
    simpa [KMap, TorusD4.slicePoint, TorusD4.delta, hk0] using iterate_two_of_steps h1 h2
  · have h1 :
        pairColorMap (m := m) 0 (((i, k), (0 : ZMod m))) = KMap (m := m) 1 (((i, k), (0 : ZMod m))) := by
          apply pairColorMap_eq_KMap_of_step (m := m) 0 1 (i, k) 0
          simp [colorMap, f0, hk0]
    have h2' :
        pairColorMap (m := m) 0 (((i, k), (1 : ZMod m))) =
          KMap (m := m) 2 (((i, k), (1 : ZMod m))) := by
            apply pairColorMap_eq_KMap_of_step (m := m) 0 2 (i, k) 1
            simp [colorMap, f0, h10]
    have h2 :
        pairColorMap (m := m) 0 (KMap (m := m) 1 (((i, k), (0 : ZMod m)))) =
          KMap (m := m) 2 (KMap (m := m) 1 (((i, k), (0 : ZMod m)))) := by
            simpa [KMap] using h2'
    simpa [KMap, TorusD4.slicePoint, TorusD4.delta, hk0] using iterate_two_of_steps h1 h2

theorem pairColorMap1_two [Fact (2 < m)] (u : P0Coord m) :
    ((pairColorMap (m := m) 1)^[2]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (2 : ZMod m)
        (u.1 + TorusD4.delta m (u.2 = (-1 : ZMod m)), u.2 + 1) := by
  rcases u with ⟨i, k⟩
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h1 :
      pairColorMap (m := m) 1 (((i, k), (0 : ZMod m))) = KMap (m := m) 2 (((i, k), (0 : ZMod m))) := by
        apply pairColorMap_eq_KMap_of_step (m := m) 1 2 (i, k) 0
        simp [colorMap, f1]
  by_cases hkneg1 : k = (-1 : ZMod m)
  · have h2' :
        pairColorMap (m := m) 1 (((i, k + 1), (1 : ZMod m))) =
          KMap (m := m) 0 (((i, k + 1), (1 : ZMod m))) := by
            apply pairColorMap_eq_KMap_of_step (m := m) 1 0 (i, k + 1) 1
            have hk1 : k + 1 = (0 : ZMod m) := by
              simpa [hkneg1]
            simp [colorMap, f1, hk1, h10]
    have h2 :
        pairColorMap (m := m) 1 (KMap (m := m) 2 (((i, k), (0 : ZMod m)))) =
          KMap (m := m) 0 (KMap (m := m) 2 (((i, k), (0 : ZMod m)))) := by
            simpa [KMap] using h2'
    simpa [KMap, TorusD4.slicePoint, TorusD4.delta, hkneg1] using iterate_two_of_steps h1 h2
  · have h2 :
        pairColorMap (m := m) 1 (KMap (m := m) 2 (((i, k), (0 : ZMod m)))) =
          KMap (m := m) 1 (KMap (m := m) 2 (((i, k), (0 : ZMod m)))) := by
            have h2' :
                pairColorMap (m := m) 1 (((i, k + 1), (1 : ZMod m))) =
                  KMap (m := m) 1 (((i, k + 1), (1 : ZMod m))) := by
                  apply pairColorMap_eq_KMap_of_step (m := m) 1 1 (i, k + 1) 1
                  have hk1 : k + 1 ≠ (0 : ZMod m) := by
                    intro hk1
                    exact hkneg1 (eq_neg_iff_add_eq_zero.mpr hk1)
                  simp [colorMap, f1, hk1, h10]
            simpa [KMap] using h2'
    simpa [KMap, TorusD4.slicePoint, TorusD4.delta, hkneg1] using iterate_two_of_steps h1 h2

theorem pairColorMap2_two [Fact (2 < m)] (u : P0Coord m) :
    ((pairColorMap (m := m) 2)^[2]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (2 : ZMod m)
        (u.1 + 2 - 2 * TorusD4.delta m (u.2 = 0), u.2) := by
  rcases u with ⟨i, k⟩
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  by_cases hk0 : k = 0
  · have h1 :
        pairColorMap (m := m) 2 (((i, k), (0 : ZMod m))) = KMap (m := m) 1 (((i, k), (0 : ZMod m))) := by
          apply pairColorMap_eq_KMap_of_step (m := m) 2 1 (i, k) 0
          simp [colorMap, f2, hk0]
    have h2' :
        pairColorMap (m := m) 2 (((i, k), (1 : ZMod m))) =
          KMap (m := m) 1 (((i, k), (1 : ZMod m))) := by
            apply pairColorMap_eq_KMap_of_step (m := m) 2 1 (i, k) 1
            simp [colorMap, f2, hk0, h10]
    have h2 :
        pairColorMap (m := m) 2 (KMap (m := m) 1 (((i, k), (0 : ZMod m)))) =
          KMap (m := m) 1 (KMap (m := m) 1 (((i, k), (0 : ZMod m)))) := by
            simpa [KMap] using h2'
    simpa [KMap, TorusD4.slicePoint, TorusD4.delta, hk0] using iterate_two_of_steps h1 h2
  · have h1 :
        pairColorMap (m := m) 2 (((i, k), (0 : ZMod m))) = KMap (m := m) 0 (((i, k), (0 : ZMod m))) := by
          apply pairColorMap_eq_KMap_of_step (m := m) 2 0 (i, k) 0
          simp [colorMap, f2, hk0]
    have h2' :
        pairColorMap (m := m) 2 (((i + 1, k), (1 : ZMod m))) =
          KMap (m := m) 0 (((i + 1, k), (1 : ZMod m))) := by
            apply pairColorMap_eq_KMap_of_step (m := m) 2 0 (i + 1, k) 1
            simp [colorMap, f2, hk0, h10]
    have h2 :
        pairColorMap (m := m) 2 (KMap (m := m) 0 (((i, k), (0 : ZMod m)))) =
          KMap (m := m) 0 (KMap (m := m) 0 (((i, k), (0 : ZMod m)))) := by
            simpa [KMap] using h2'
    have hsum : (i + 1 : ZMod m) + 1 = i + 2 := by ring
    simpa [KMap, TorusD4.slicePoint, TorusD4.delta, hk0, hsum] using iterate_two_of_steps h1 h2

def FMap : Color → P0Coord m → P0Coord m
  | 0 => F0 (m := m)
  | 1 => F1 (m := m)
  | 2 => F2 (m := m)

theorem iterate_m_pairColorMap_slicePoint_zero_F0 [Fact (2 < m)] (u : P0Coord m) :
    ((pairColorMap (m := m) 0)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (0 : ZMod m) (F0 (m := m) u) := by
  have hm2 : 2 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) hm2⟩
  have hm : 2 ≤ m := le_of_lt hm2
  have hmSplit : m = (m - 2) + 2 := by omega
  calc
    ((pairColorMap (m := m) 0)^[m]) (TorusD4.slicePoint (0 : ZMod m) u)
        = ((pairColorMap (m := m) 0)^[(m - 2) + 2]) (TorusD4.slicePoint (0 : ZMod m) u) := by
            convert
              (rfl :
                ((pairColorMap (m := m) 0)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
                  ((pairColorMap (m := m) 0)^[m]) (TorusD4.slicePoint (0 : ZMod m) u))
            · omega
    _ = ((pairColorMap (m := m) 0)^[m - 2])
          (((pairColorMap (m := m) 0)^[2]) (TorusD4.slicePoint (0 : ZMod m) u)) := by
            simpa using
              (Function.iterate_add_apply (pairColorMap (m := m) 0) (m - 2) 2
                (TorusD4.slicePoint (0 : ZMod m) u))
    _ = ((pairColorMap (m := m) 0)^[m - 2])
          (TorusD4.slicePoint (2 : ZMod m) (u.1 + TorusD4.delta m (u.2 = 0), u.2 + 1)) := by
            rw [pairColorMap0_two (m := m) u]
    _ = ((KMap (m := m) 0)^[m - 2])
          (TorusD4.slicePoint (2 : ZMod m) (u.1 + TorusD4.delta m (u.2 = 0), u.2 + 1)) := by
            simpa [TorusD4.slicePoint] using
              iterate_pairColorMap_from_two_eq_iterate_KMap (m := m) 0 (m - 2)
                (u.1 + TorusD4.delta m (u.2 = 0), u.2 + 1) (le_rfl)
    _ = TorusD4.slicePoint ((2 : ZMod m) + (((m - 2 : ℕ) : ZMod m)))
          (u.1 + TorusD4.delta m (u.2 = 0) + (((m - 2 : ℕ) : ZMod m)), u.2 + 1) := by
            simpa [TorusD4.slicePoint] using
              iterate_K0 (m := m) (m - 2) (u.1 + TorusD4.delta m (u.2 = 0)) (u.2 + 1) (2 : ZMod m)
    _ = TorusD4.slicePoint (0 : ZMod m) (F0 (m := m) u) := by
          rw [natCast_sub_two (m := m) hm]
          rcases u with ⟨i, k⟩
          ext <;> simp [TorusD4.slicePoint, F0]
          ring

theorem iterate_m_pairColorMap_slicePoint_zero_F1 [Fact (2 < m)] (u : P0Coord m) :
    ((pairColorMap (m := m) 1)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (0 : ZMod m) (F1 (m := m) u) := by
  have hm2 : 2 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) hm2⟩
  have hm : 2 ≤ m := le_of_lt hm2
  have hmSplit : m = (m - 2) + 2 := by omega
  calc
    ((pairColorMap (m := m) 1)^[m]) (TorusD4.slicePoint (0 : ZMod m) u)
        = ((pairColorMap (m := m) 1)^[(m - 2) + 2]) (TorusD4.slicePoint (0 : ZMod m) u) := by
            convert
              (rfl :
                ((pairColorMap (m := m) 1)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
                  ((pairColorMap (m := m) 1)^[m]) (TorusD4.slicePoint (0 : ZMod m) u))
            · omega
    _ = ((pairColorMap (m := m) 1)^[m - 2])
          (((pairColorMap (m := m) 1)^[2]) (TorusD4.slicePoint (0 : ZMod m) u)) := by
            simpa using
              (Function.iterate_add_apply (pairColorMap (m := m) 1) (m - 2) 2
                (TorusD4.slicePoint (0 : ZMod m) u))
    _ = ((pairColorMap (m := m) 1)^[m - 2])
          (TorusD4.slicePoint (2 : ZMod m)
            (u.1 + TorusD4.delta m (u.2 = (-1 : ZMod m)), u.2 + 1)) := by
            rw [pairColorMap1_two (m := m) u]
    _ = ((KMap (m := m) 1)^[m - 2])
          (TorusD4.slicePoint (2 : ZMod m)
            (u.1 + TorusD4.delta m (u.2 = (-1 : ZMod m)), u.2 + 1)) := by
            simpa [TorusD4.slicePoint] using
              iterate_pairColorMap_from_two_eq_iterate_KMap (m := m) 1 (m - 2)
                (u.1 + TorusD4.delta m (u.2 = (-1 : ZMod m)), u.2 + 1) (le_rfl)
    _ = TorusD4.slicePoint ((2 : ZMod m) + (((m - 2 : ℕ) : ZMod m)))
          (u.1 + TorusD4.delta m (u.2 = (-1 : ZMod m)), u.2 + 1) := by
            simpa [TorusD4.slicePoint] using
              iterate_K1 (m := m) (m - 2)
                (u.1 + TorusD4.delta m (u.2 = (-1 : ZMod m)), u.2 + 1) (2 : ZMod m)
    _ = TorusD4.slicePoint (0 : ZMod m) (F1 (m := m) u) := by
          rw [natCast_sub_two (m := m) hm]
          rcases u with ⟨i, k⟩
          ext <;> simp [TorusD4.slicePoint, F1]

theorem iterate_m_pairColorMap_slicePoint_zero_F2 [Fact (2 < m)] (u : P0Coord m) :
    ((pairColorMap (m := m) 2)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (0 : ZMod m) (F2 (m := m) u) := by
  have hm2 : 2 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) hm2⟩
  have hm : 2 ≤ m := le_of_lt hm2
  have hmSplit : m = (m - 2) + 2 := by omega
  calc
    ((pairColorMap (m := m) 2)^[m]) (TorusD4.slicePoint (0 : ZMod m) u)
        = ((pairColorMap (m := m) 2)^[(m - 2) + 2]) (TorusD4.slicePoint (0 : ZMod m) u) := by
            convert
              (rfl :
                ((pairColorMap (m := m) 2)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
                  ((pairColorMap (m := m) 2)^[m]) (TorusD4.slicePoint (0 : ZMod m) u))
            · omega
    _ = ((pairColorMap (m := m) 2)^[m - 2])
          (((pairColorMap (m := m) 2)^[2]) (TorusD4.slicePoint (0 : ZMod m) u)) := by
            simpa using
              (Function.iterate_add_apply (pairColorMap (m := m) 2) (m - 2) 2
                (TorusD4.slicePoint (0 : ZMod m) u))
    _ = ((pairColorMap (m := m) 2)^[m - 2])
          (TorusD4.slicePoint (2 : ZMod m)
            (u.1 + 2 - 2 * TorusD4.delta m (u.2 = 0), u.2)) := by
            rw [pairColorMap2_two (m := m) u]
    _ = ((KMap (m := m) 2)^[m - 2])
          (TorusD4.slicePoint (2 : ZMod m)
            (u.1 + 2 - 2 * TorusD4.delta m (u.2 = 0), u.2)) := by
            simpa [TorusD4.slicePoint] using
              iterate_pairColorMap_from_two_eq_iterate_KMap (m := m) 2 (m - 2)
                (u.1 + 2 - 2 * TorusD4.delta m (u.2 = 0), u.2) (le_rfl)
    _ = TorusD4.slicePoint ((2 : ZMod m) + (((m - 2 : ℕ) : ZMod m)))
          (u.1 + 2 - 2 * TorusD4.delta m (u.2 = 0), u.2 + (((m - 2 : ℕ) : ZMod m))) := by
            simpa [TorusD4.slicePoint] using
              iterate_K2 (m := m) (m - 2)
                (u.1 + 2 - 2 * TorusD4.delta m (u.2 = 0)) u.2 (2 : ZMod m)
    _ = TorusD4.slicePoint (0 : ZMod m) (F2 (m := m) u) := by
          rw [natCast_sub_two (m := m) hm]
          rcases u with ⟨i, k⟩
          ext <;> simp [TorusD4.slicePoint, F2]
          ring

theorem iterate_m_pairColorMap_slicePoint_zero [Fact (2 < m)] (c : Color) (u : P0Coord m) :
    ((pairColorMap (m := m) c)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (0 : ZMod m) (FMap (m := m) c u) := by
  fin_cases c
  · simpa [FMap] using iterate_m_pairColorMap_slicePoint_zero_F0 (m := m) u
  · simpa [FMap] using iterate_m_pairColorMap_slicePoint_zero_F1 (m := m) u
  · simpa [FMap] using iterate_m_pairColorMap_slicePoint_zero_F2 (m := m) u

theorem firstReturn_eq_FMap [Fact (2 < m)] (c : Color) (u : P0Coord m) :
    ((colorMap (m := m) c)^[m]) (phiLayer (m := m) u 0) = phiLayer (m := m) (FMap (m := m) c u) 0 := by
  have hsemi := splitPointEquiv_semiconj_pairColorMap (m := m) c
  apply point_eq_phiLayer_of_splitPointEquiv_eq (m := m)
  calc
    splitPointEquiv (m := m) (((colorMap (m := m) c)^[m]) (phiLayer (m := m) u 0))
        = ((pairColorMap (m := m) c)^[m]) (TorusD4.slicePoint (0 : ZMod m) u) := by
            simpa [TorusD4.slicePoint] using (hsemi.iterate_right m).eq (phiLayer (m := m) u 0)
    _ = TorusD4.slicePoint (0 : ZMod m) (FMap (m := m) c u) := by
          rw [iterate_m_pairColorMap_slicePoint_zero (m := m) c u]

theorem hasCycle_FMap [Fact (Odd m)] (c : Color) :
    TorusD4.HasCycle (m * m) (FMap (m := m) c) := by
  letI : Fact (0 < m) := ⟨pos_of_odd (m := m)⟩
  fin_cases c
  · simpa [FMap] using hasCycle_F0 (m := m)
  · simpa [FMap] using hasCycle_F1 (m := m)
  · simpa [FMap] using hasCycle_F2 (m := m)

theorem iterate_mul_pairColorMap_slicePoint_zero [Fact (2 < m)] (c : Color) :
    ∀ t u, ((pairColorMap (m := m) c)^[m * t]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[t]) u) := by
  have hm2 : 2 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) hm2⟩
  exact TorusD4.iterate_mul_slicePoint (m := m)
    (F := pairColorMap (m := m) c) (T := FMap (m := m) c) (q0 := (0 : ZMod m))
    (hreturn := iterate_m_pairColorMap_slicePoint_zero (m := m) c)

theorem iterate_add_mul_pairColorMap_slicePoint_zero [Fact (2 < m)] (c : Color)
    (t r : ℕ) (u : P0Coord m) :
    ((pairColorMap (m := m) c)^[m * t + r]) (TorusD4.slicePoint (0 : ZMod m) u) =
      ((pairColorMap (m := m) c)^[r]) (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[t]) u)) := by
  calc
    ((pairColorMap (m := m) c)^[m * t + r]) (TorusD4.slicePoint (0 : ZMod m) u)
        = ((pairColorMap (m := m) c)^[r])
            (((pairColorMap (m := m) c)^[m * t]) (TorusD4.slicePoint (0 : ZMod m) u)) := by
              simpa [Nat.add_comm] using
                (Function.iterate_add_apply (pairColorMap (m := m) c) r (m * t)
                  (TorusD4.slicePoint (0 : ZMod m) u))
    _ = ((pairColorMap (m := m) c)^[r])
          (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[t]) u)) := by
            rw [iterate_mul_pairColorMap_slicePoint_zero (m := m) c t u]

theorem cycleOn_pairColorMap_of_cycleOn_FMap [Fact (2 < m)] (c : Color)
    {u : P0Coord m} (hc : TorusD4.CycleOn (m * m) (FMap (m := m) c) u) :
    TorusD4.CycleOn (m * (m * m)) (pairColorMap (m := m) c) (TorusD4.slicePoint (0 : ZMod m) u) := by
  have hm2 : 2 < m := Fact.out
  have hm0 : 0 < m := lt_trans (by decide : 0 < 2) hm2
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (0 < m * m) := ⟨by positivity⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  letI : Fintype (FullCoord m) := inferInstance
  refine ⟨?_, ?_⟩
  · have hinj :
        Function.Injective fun i : Fin (m * (m * m)) =>
          ((pairColorMap (m := m) c)^[i.1]) (TorusD4.slicePoint (0 : ZMod m) u) := by
        intro i j hij
        let ti : ℕ := i.1 / m
        let tj : ℕ := j.1 / m
        let ri : ℕ := i.1 % m
        let rj : ℕ := j.1 % m
        have hi_decomp : i.1 = m * ti + ri := by
          dsimp [ti, ri]
          exact (Nat.div_add_mod i.1 m).symm
        have hj_decomp : j.1 = m * tj + rj := by
          dsimp [tj, rj]
          exact (Nat.div_add_mod j.1 m).symm
        have hti_lt : ti < m * m := by
          dsimp [ti]
          have hi_bound : i.1 < (m * m) * m := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using i.2
          exact (Nat.div_lt_iff_lt_mul hm0).2 hi_bound
        have htj_lt : tj < m * m := by
          dsimp [tj]
          have hj_bound : j.1 < (m * m) * m := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using j.2
          exact (Nat.div_lt_iff_lt_mul hm0).2 hj_bound
        have hri_lt : ri < m := by
          dsimp [ri]
          exact Nat.mod_lt _ hm0
        have hrj_lt : rj < m := by
          dsimp [rj]
          exact Nat.mod_lt _ hm0
        change
          ((pairColorMap (m := m) c)^[i.1]) (TorusD4.slicePoint (0 : ZMod m) u) =
            ((pairColorMap (m := m) c)^[j.1]) (TorusD4.slicePoint (0 : ZMod m) u) at hij
        rw [hi_decomp, iterate_add_mul_pairColorMap_slicePoint_zero (m := m) c ti ri u,
          hj_decomp, iterate_add_mul_pairColorMap_slicePoint_zero (m := m) c tj rj u] at hij
        have hcast : ((ri : ℕ) : ZMod m) = ((rj : ℕ) : ZMod m) := by
          simpa [TorusD4.slicePoint] using congrArg Prod.snd hij
        have hrem_mod : ri % m = rj % m := by
          exact (ZMod.natCast_eq_natCast_iff' ri rj m).1 hcast
        have hrem : ri = rj := by
          rwa [Nat.mod_eq_of_lt hri_lt, Nat.mod_eq_of_lt hrj_lt] at hrem_mod
        have hij_shift :
            ((pairColorMap (m := m) c)^[m - ri])
                (((pairColorMap (m := m) c)^[ri])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti]) u))) =
              ((pairColorMap (m := m) c)^[m - ri])
                (((pairColorMap (m := m) c)^[rj])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u))) := by
          exact congrArg ((pairColorMap (m := m) c)^[m - ri]) hij
        have hleft :
            ((pairColorMap (m := m) c)^[m - ri])
                (((pairColorMap (m := m) c)^[ri])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti]) u))) =
              TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti + 1]) u) := by
          calc
            ((pairColorMap (m := m) c)^[m - ri])
                (((pairColorMap (m := m) c)^[ri])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti]) u)))
                = ((pairColorMap (m := m) c)^[m - ri + ri])
                    (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti]) u)) := by
                      symm
                      simpa using
                        (Function.iterate_add_apply (pairColorMap (m := m) c) (m - ri) ri
                          (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti]) u)))
            _ = ((pairColorMap (m := m) c)^[m])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti]) u)) := by
                    rw [Nat.sub_add_cancel (Nat.le_of_lt hri_lt)]
            _ = TorusD4.slicePoint (0 : ZMod m)
                  (FMap (m := m) c (((FMap (m := m) c)^[ti]) u)) := by
                    rw [iterate_m_pairColorMap_slicePoint_zero (m := m) c (((FMap (m := m) c)^[ti]) u)]
            _ = TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti + 1]) u) := by
                  rw [Function.iterate_succ_apply']
        have hright0 :
            ((pairColorMap (m := m) c)^[m - rj])
                (((pairColorMap (m := m) c)^[rj])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u))) =
              TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj + 1]) u) := by
          calc
            ((pairColorMap (m := m) c)^[m - rj])
                (((pairColorMap (m := m) c)^[rj])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u)))
                = ((pairColorMap (m := m) c)^[m - rj + rj])
                    (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u)) := by
                      symm
                      simpa using
                        (Function.iterate_add_apply (pairColorMap (m := m) c) (m - rj) rj
                          (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u)))
            _ = ((pairColorMap (m := m) c)^[m])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u)) := by
                    rw [Nat.sub_add_cancel (Nat.le_of_lt hrj_lt)]
            _ = TorusD4.slicePoint (0 : ZMod m)
                  (FMap (m := m) c (((FMap (m := m) c)^[tj]) u)) := by
                    rw [iterate_m_pairColorMap_slicePoint_zero (m := m) c (((FMap (m := m) c)^[tj]) u)]
            _ = TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj + 1]) u) := by
                  rw [Function.iterate_succ_apply']
        have hright :
            ((pairColorMap (m := m) c)^[m - ri])
                (((pairColorMap (m := m) c)^[rj])
                  (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u))) =
              TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj + 1]) u) := by
          simpa [hrem] using hright0
        have hslice :
            TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti + 1]) u) =
              TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj + 1]) u) := by
          calc
            TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti + 1]) u)
                = ((pairColorMap (m := m) c)^[m - ri])
                    (((pairColorMap (m := m) c)^[ri])
                      (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[ti]) u))) := by
                        symm
                        exact hleft
            _ = ((pairColorMap (m := m) c)^[m - ri])
                  (((pairColorMap (m := m) c)^[rj])
                    (TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj]) u))) :=
                      hij_shift
            _ = TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[tj + 1]) u) := hright
        have hu_eq : ((FMap (m := m) c)^[ti + 1]) u = ((FMap (m := m) c)^[tj + 1]) u := by
          simpa [TorusD4.slicePoint] using congrArg Prod.fst hslice
        have ht_mod : ti + 1 ≡ tj + 1 [MOD m * m] :=
          TorusD4.cycleOn_iterate_modEq (N := m * m) (f := FMap (m := m) c) (x := u) hc hu_eq
        have ht'_mod : ti ≡ tj [MOD m * m] := Nat.ModEq.add_right_cancel' 1 <| by
          simpa [Nat.add_comm] using ht_mod
        have ht : ti = tj := by
          simpa [Nat.ModEq, Nat.mod_eq_of_lt hti_lt, Nat.mod_eq_of_lt htj_lt] using ht'_mod
        apply Fin.eq_of_val_eq
        calc
          i.1 = m * ti + ri := hi_decomp
          _ = m * tj + rj := by rw [ht, hrem]
          _ = j.1 := hj_decomp.symm
    exact (Fintype.bijective_iff_injective_and_card _).2
      ⟨hinj, by simp [FullCoord, P0Coord, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩
  · calc
      ((pairColorMap (m := m) c)^[m * (m * m)]) (TorusD4.slicePoint (0 : ZMod m) u)
          = TorusD4.slicePoint (0 : ZMod m) (((FMap (m := m) c)^[m * m]) u) := by
              rw [iterate_mul_pairColorMap_slicePoint_zero (m := m) c (m * m) u]
      _ = TorusD4.slicePoint (0 : ZMod m) u := by rw [hc.2]

theorem hasCycle_pairColorMap [Fact (Odd m)] [Fact (2 < m)] (c : Color) :
    TorusD4.HasCycle (m ^ 3) (pairColorMap (m := m) c) := by
  rcases hasCycle_FMap (m := m) c with ⟨u, hu⟩
  refine ⟨TorusD4.slicePoint (0 : ZMod m) u, ?_⟩
  simpa [pow_succ, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    cycleOn_pairColorMap_of_cycleOn_FMap (m := m) c hu

theorem hasCycle_colorMap [Fact (Odd m)] [Fact (2 < m)] (c : Color) :
    TorusD4.HasCycle (m ^ 3) (colorMap (m := m) c) := by
  rcases hasCycle_pairColorMap (m := m) c with ⟨z, hz⟩
  refine ⟨(splitPointEquiv (m := m)).symm z, ?_⟩
  exact TorusD4.cycleOn_conj (splitPointEquiv (m := m)).symm
    (f := pairColorMap (m := m) c) (g := colorMap (m := m) c)
    (splitPointEquiv_symm_semiconj_colorMap (m := m) c) hz

theorem all_colors_haveCycle [Fact (Odd m)] [Fact (2 < m)] :
    ∀ c : Color, TorusD4.HasCycle (m ^ 3) (colorMap (m := m) c) := by
  intro c
  exact hasCycle_colorMap (m := m) c

end TorusD3Odd
