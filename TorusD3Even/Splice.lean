import TorusD3Even.Counting
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace TorusD3Even

variable {α : Type*}

/-
The intended model is a finite collection of ordered blocks whose terminal points
wrap to the initial point of the next block in cyclic order.
-/

abbrev SplicePoint {r : ℕ} (len : Fin r → ℕ) := Sigma fun j : Fin r => Fin (len j + 1)

private def zeroBlock {r : ℕ} [Fact (0 < r)] : Fin r :=
  ⟨0, Fact.out⟩

def nextBlock {r : ℕ} [Fact (0 < r)] (j : Fin r) : Fin r :=
  ⟨(j.1 + 1) % r, Nat.mod_lt _ Fact.out⟩

def spliceStart {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) : SplicePoint len :=
  ⟨zeroBlock, 0⟩

def cyclicSpliceSucc {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) :
    SplicePoint len → SplicePoint len
  | ⟨j, s⟩ =>
      if hs : s.1 + 1 < len j + 1 then
        ⟨j, ⟨s.1 + 1, hs⟩⟩
      else
        ⟨nextBlock j, 0⟩

def castFinFun {n m : ℕ} (h : n = m) (f : Fin n → α) : Fin m → α := fun i =>
  f (Fin.cast h.symm i)

@[simp] theorem castFinFun_apply {n m : ℕ} (h : n = m) (f : Fin n → α) (i : Fin m) :
    castFinFun h f i = f (Fin.cast h.symm i) := rfl

theorem castFinFun_injective {n m : ℕ} (h : n = m) {f : Fin n → α}
    (hf : Function.Injective f) :
    Function.Injective (castFinFun h f) := by
  intro i j hij
  apply Fin.ext
  have hcast : Fin.cast h.symm i = Fin.cast h.symm j := hf hij
  simpa using congrArg Fin.val hcast

private def spliceEmbed {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) (j : Fin r) : SplicePoint len :=
  ⟨j, 0⟩

private theorem spliceEmbed_injective {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) :
    Function.Injective (spliceEmbed len) := by
  intro j k h
  simpa [spliceEmbed] using congrArg Sigma.fst h

private theorem iterate_nextBlock_zero_of_lt
    {r : ℕ} [Fact (0 < r)] {n : ℕ} (hn : n < r) :
    (nextBlock^[n]) (zeroBlock : Fin r) = ⟨n, hn⟩ := by
  induction n with
  | zero =>
      apply Fin.ext
      simp [zeroBlock]
  | succ n ih =>
      have hn' : n < r := Nat.lt_trans (Nat.lt_succ_self n) hn
      rw [Function.iterate_succ_apply', ih hn']
      apply Fin.ext
      simp [nextBlock, Nat.mod_eq_of_lt hn]

private theorem cycleOn_nextBlock {r : ℕ} [Fact (0 < r)] :
    TorusD4.CycleOn r nextBlock (zeroBlock : Fin r) := by
  have hperiod : (nextBlock^[r]) (zeroBlock : Fin r) = zeroBlock := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (n := r) (Nat.ne_of_gt (Fact.out : 0 < r))
    cases hk
    rw [Function.iterate_succ_apply', iterate_nextBlock_zero_of_lt (r := k + 1) (n := k)
      (Nat.lt_succ_self k)]
    apply Fin.ext
    simp [nextBlock, zeroBlock]
  have hminimal :
      ∀ n, 0 < n → n < r → (nextBlock^[n]) (zeroBlock : Fin r) ≠ zeroBlock := by
    intro n hn0 hnLt h
    have hfin : (⟨n, hnLt⟩ : Fin r) = zeroBlock := by
      calc
        (⟨n, hnLt⟩ : Fin r) = (nextBlock^[n]) (zeroBlock : Fin r) := by
          symm
          exact iterate_nextBlock_zero_of_lt (r := r) (n := n) hnLt
        _ = zeroBlock := h
    have hnEq0 : n = 0 := by
      simpa [zeroBlock] using congrArg Fin.val hfin
    exact Nat.ne_of_gt hn0 hnEq0
  have hperiodCard : (nextBlock^[Fintype.card (Fin r)]) (zeroBlock : Fin r) = zeroBlock := by
    simpa using hperiod
  have hminimalCard :
      ∀ n, 0 < n → n < Fintype.card (Fin r) → (nextBlock^[n]) (zeroBlock : Fin r) ≠ zeroBlock := by
    intro n hn0 hnLt
    apply hminimal n hn0
    simpa using hnLt
  simpa using
    (cycleOn_of_period_card (α := Fin r) (F := nextBlock) (x := (zeroBlock : Fin r))
      hperiodCard hminimalCard)

private theorem iterate_cyclicSpliceSucc_start
    {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) (j : Fin r) :
    ∀ {n : ℕ} (hn : n ≤ len j),
      ((cyclicSpliceSucc len)^[n]) (spliceEmbed len j) = ⟨j, ⟨n, Nat.lt_succ_of_le hn⟩⟩ := by
  intro n hn
  induction n with
  | zero =>
      have hs : (0 : Fin (len j + 1)) = ⟨0, Nat.lt_succ_of_le hn⟩ := by
        apply Fin.ext
        simp
      simpa [spliceEmbed] using congrArg (Sigma.mk j) hs
  | succ n ih =>
      have hn' : n ≤ len j := by omega
      rw [Function.iterate_succ_apply', ih hn']
      have hs : n + 1 < len j + 1 := Nat.lt_succ_of_le hn
      simp [cyclicSpliceSucc, hs]

private theorem block_return_cyclicSpliceSucc
    {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) (j : Fin r) :
    ((cyclicSpliceSucc len)^[len j + 1]) (spliceEmbed len j) = spliceEmbed len (nextBlock j) := by
  rw [Function.iterate_succ_apply',
    iterate_cyclicSpliceSucc_start (len := len) (j := j) (n := len j) le_rfl]
  have hs : ¬ (len j + 1 < len j + 1) := by omega
  simp [spliceEmbed, cyclicSpliceSucc, hs]

private theorem not_mem_range_spliceEmbed_mid
    {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) (j : Fin r) {n : ℕ}
    (hn0 : 0 < n) (hn : n < len j + 1) :
    ((cyclicSpliceSucc len)^[n]) (spliceEmbed len j) ∉ Set.range (spliceEmbed len) := by
  have hn' : n ≤ len j := by omega
  rw [iterate_cyclicSpliceSucc_start (len := len) (j := j) (n := n) hn']
  intro h
  rcases h with ⟨k, hk⟩
  have hnEq0 : n = 0 := by
    simpa [spliceEmbed] using (congrArg (fun p : SplicePoint len => p.2.1) hk).symm
  exact Nat.ne_of_gt hn0 hnEq0

private theorem blockTime_eq_sum_iterates {β : Type*}
    (T : β → β) (rho : β → ℕ) (x0 : β) :
    ∀ M, blockTime T rho x0 M = Finset.sum (Finset.range M) (fun i => rho ((T^[i]) x0)) := by
  intro M
  induction M with
  | zero =>
      simp [blockTime]
  | succ M ih =>
      rw [blockTime_succ, ih, Finset.sum_range_succ]

/-
First theorem target: the abstract sigma-model itself is one cycle.
This is the Lean form of the manuscript splice graph lemma specialized to a
cyclic permutation on the block labels.
-/
theorem cycleOn_cyclicSpliceSucc
    {r : ℕ} [Fact (0 < r)] (len : Fin r → ℕ) :
    TorusD4.CycleOn (Fintype.card (SplicePoint len)) (cyclicSpliceSucc len) (spliceStart len) := by
  let rho : Fin r → ℕ := fun j => len j + 1
  have hcycleBlocks : TorusD4.CycleOn r nextBlock (zeroBlock : Fin r) := cycleOn_nextBlock
  have hreturn :
      ∀ j, ((cyclicSpliceSucc len)^[rho j]) (spliceEmbed len j) = spliceEmbed len (nextBlock j) := by
    intro j
    simpa [rho] using block_return_cyclicSpliceSucc len j
  have hfirst :
      ∀ j n, 0 < n → n < rho j →
        ((cyclicSpliceSucc len)^[n]) (spliceEmbed len j) ∉ Set.range (spliceEmbed len) := by
    intro j n hn0 hn
    simpa [rho] using not_mem_range_spliceEmbed_mid len j hn0 hn
  have hsumBlocks :
      blockTime nextBlock rho (zeroBlock : Fin r) r
        = Finset.sum (Finset.range r) (fun i => rho ((nextBlock^[i]) (zeroBlock : Fin r))) := by
    simpa [rho] using blockTime_eq_sum_iterates nextBlock rho (zeroBlock : Fin r) r
  let g : ℕ → ℕ := fun i => if h : i < r then len ⟨i, h⟩ + 1 else 0
  have hsumRange :
      Finset.sum (Finset.range r) (fun i => rho ((nextBlock^[i]) (zeroBlock : Fin r)))
        = Finset.sum (Finset.range r) g := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    simp [rho, g, iterate_nextBlock_zero_of_lt (r := r) (n := i) hi', hi']
  have hsumFin :
      Finset.sum (Finset.range r) g = (∑ j : Fin r, (len j + 1)) := by
    symm
    simpa [g] using (Fin.sum_univ_eq_sum_range g r)
  have hcard : Fintype.card (SplicePoint len) = ∑ j : Fin r, (len j + 1) := by
    simpa [SplicePoint] using
      (Fintype.card_sigma (α := fun j : Fin r => Fin (len j + 1)))
  have hsum : blockTime nextBlock rho (zeroBlock : Fin r) r = Fintype.card (SplicePoint len) := by
    calc
      blockTime nextBlock rho (zeroBlock : Fin r) r
          = Finset.sum (Finset.range r) (fun i => rho ((nextBlock^[i]) (zeroBlock : Fin r))) := hsumBlocks
      _ = Finset.sum (Finset.range r) g := hsumRange
      _ = ∑ j : Fin r, (len j + 1) := hsumFin
      _ = Fintype.card (SplicePoint len) := hcard.symm
  simpa [spliceStart, spliceEmbed] using
    (firstReturn_counting (α := SplicePoint len) (β := Fin r)
      (F := cyclicSpliceSucc len) (embed := spliceEmbed len)
      (hembed := spliceEmbed_injective len)
      (T := nextBlock) (rho := rho) (M := r) (x0 := (zeroBlock : Fin r))
      (hcycle := hcycleBlocks) (hreturn := hreturn) (hfirst := hfirst) (hsum := hsum))

/-
Second theorem target: transport the sigma-model cycle statement across an
explicit equivalence to the concrete lane set for a given color.
-/
theorem cycleOn_of_spliceBlocks
    {r : ℕ} [Fact (0 < r)] [Fintype α]
    (len : Fin r → ℕ)
    (e : SplicePoint len ≃ α)
    (T : α → α)
    (hstep :
      ∀ j (s : Fin (len j + 1)) (hs : s.1 + 1 < len j + 1),
        T (e ⟨j, s⟩) = e ⟨j, ⟨s.1 + 1, hs⟩⟩)
    (hwrap :
      ∀ j,
        T (e ⟨j, ⟨len j, Nat.lt_succ_self _⟩⟩) = e ⟨nextBlock j, 0⟩) :
    TorusD4.CycleOn (Fintype.card α) T (e (spliceStart len)) := by
  have hcycleSigma :
      TorusD4.CycleOn (Fintype.card (SplicePoint len)) (cyclicSpliceSucc len) (spliceStart len) :=
    cycleOn_cyclicSpliceSucc len
  have hcomm : ∀ p : SplicePoint len, T (e p) = e (cyclicSpliceSucc len p) := by
    intro p
    rcases p with ⟨j, s⟩
    by_cases hs : s.1 + 1 < len j + 1
    · simpa [cyclicSpliceSucc, hs] using hstep j s hs
    · have hsVal : s.1 = len j := by
        have hsLe : s.1 ≤ len j := Nat.le_of_lt_succ s.2
        omega
      have hsEq : s = ⟨len j, Nat.lt_succ_self _⟩ := by
        apply Fin.ext
        simpa [hsVal]
      cases hsEq
      simpa [cyclicSpliceSucc, hs] using hwrap j
  have hcommIter :
      ∀ (n : ℕ) (p : SplicePoint len),
        (T^[n]) (e p) = e (((cyclicSpliceSucc len)^[n]) p) := by
    intro n p
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        exact hcomm _
  have hcard : Fintype.card (SplicePoint len) = Fintype.card α := Fintype.card_congr e
  have hperiod : (T^[Fintype.card α]) (e (spliceStart len)) = e (spliceStart len) := by
    rw [← hcard]
    calc
      (T^[Fintype.card (SplicePoint len)]) (e (spliceStart len))
          = e ((((cyclicSpliceSucc len)^[Fintype.card (SplicePoint len)]) (spliceStart len))) :=
              hcommIter _ _
      _ = e (spliceStart len) := by
            simpa using hcycleSigma.2
  have hminimal :
      ∀ n, 0 < n → n < Fintype.card α → (T^[n]) (e (spliceStart len)) ≠ e (spliceStart len) := by
    intro n hn0 hnLt hfix
    have hnLt' : n < Fintype.card (SplicePoint len) := by
      simpa [hcard] using hnLt
    have hfix' : ((cyclicSpliceSucc len)^[n]) (spliceStart len) = spliceStart len := by
      apply e.injective
      calc
        e ((((cyclicSpliceSucc len)^[n]) (spliceStart len)))
            = (T^[n]) (e (spliceStart len)) := by
                symm
                exact hcommIter n (spliceStart len)
        _ = e (spliceStart len) := hfix
    have hcardPos : 0 < Fintype.card (SplicePoint len) := by
      simpa using (Fintype.card_pos_iff.mpr ⟨spliceStart len⟩)
    have hnEq0 : n = 0 := by
      exact TorusD4.cycleOn_iterate_injective hcycleSigma hnLt' hcardPos (by simpa using hfix')
    exact Nat.ne_of_gt hn0 hnEq0
  exact cycleOn_of_period_card hperiod hminimal

private theorem appendPoint_right_bound
    {n k i : ℕ} (hi : i < n + k + 2) (hleft : ¬ i < n + 1) :
    i - (n + 1) < k + 1 := by
  omega

def appendPoint {n k : ℕ} (f : Fin (n + 1) → α) (g : Fin (k + 1) → α) :
    Fin (n + k + 2) → α := fun s =>
  if hs : s.1 < n + 1 then
    f ⟨s.1, hs⟩
  else
    g ⟨s.1 - (n + 1), appendPoint_right_bound s.2 hs⟩

theorem appendPoint_apply_left
    {n k : ℕ} {f : Fin (n + 1) → α} {g : Fin (k + 1) → α}
    {i : ℕ} (hi : i < n + 1) (hmem : i < n + k + 2) :
    appendPoint f g ⟨i, hmem⟩ = f ⟨i, hi⟩ := by
  simp [appendPoint, hi]

theorem appendPoint_apply_right
    {n k : ℕ} {f : Fin (n + 1) → α} {g : Fin (k + 1) → α}
    {i : ℕ} (hi : ¬ i < n + 1) (hmem : i < n + k + 2) :
    appendPoint f g ⟨i, hmem⟩ =
      g ⟨i - (n + 1), appendPoint_right_bound hmem hi⟩ := by
  simp [appendPoint, hi]

theorem appendPoint_injective
    {n k : ℕ} {f : Fin (n + 1) → α} {g : Fin (k + 1) → α}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisj : ∀ s t, f s ≠ g t) :
    Function.Injective (appendPoint f g) := by
  intro s t h
  by_cases hs : s.1 < n + 1
  · by_cases ht : t.1 < n + 1
    · apply Fin.ext
      have hfg : f ⟨s.1, hs⟩ = f ⟨t.1, ht⟩ := by
        simpa [appendPoint, hs, ht] using h
      exact congrArg (fun u : Fin (n + 1) => u.1) (hf hfg)
    · let tt : Fin (k + 1) := ⟨t.1 - (n + 1), appendPoint_right_bound t.2 ht⟩
      have hfg : f ⟨s.1, hs⟩ = g tt := by
        simpa [appendPoint, hs, ht, tt] using h
      exact False.elim ((hdisj ⟨s.1, hs⟩ tt) hfg)
  · by_cases ht : t.1 < n + 1
    · let ss : Fin (k + 1) := ⟨s.1 - (n + 1), appendPoint_right_bound s.2 hs⟩
      have hfg : g ss = f ⟨t.1, ht⟩ := by
        simpa [appendPoint, hs, ht, ss] using h
      exact False.elim ((hdisj ⟨t.1, ht⟩ ss) hfg.symm)
    · let ss : Fin (k + 1) := ⟨s.1 - (n + 1), appendPoint_right_bound s.2 hs⟩
      let tt : Fin (k + 1) := ⟨t.1 - (n + 1), appendPoint_right_bound t.2 ht⟩
      apply Fin.ext
      have hfg : g ss = g tt := by
        simpa [appendPoint, hs, ht, ss, tt] using h
      have hst : ss = tt := hg hfg
      have hval : s.1 - (n + 1) = t.1 - (n + 1) := by
        simpa [ss, tt] using congrArg (fun u : Fin (k + 1) => u.1) hst
      omega

section ArithmeticBlocks

private theorem affinePoint_bound
    {m a d n k : ℕ} (hbound : a + d * n < m) (hk : k ≤ n) :
    a + d * k < m := by
  have hmul : d * k ≤ d * n := Nat.mul_le_mul_left d hk
  omega

def affinePoint (m a d n : ℕ) (hbound : a + d * n < m) :
    Fin (n + 1) → Fin m := fun s =>
  ⟨a + d * s.1, affinePoint_bound hbound (Nat.le_of_lt_succ s.2)⟩

@[simp] theorem affinePoint_val
    {m a d n : ℕ} {hbound : a + d * n < m} (s : Fin (n + 1)) :
    (affinePoint m a d n hbound s).1 = a + d * s.1 := rfl

@[simp] theorem affinePoint_zero_val
    {m a d n : ℕ} {hbound : a + d * n < m} :
    (affinePoint m a d n hbound 0).1 = a := by
  simp [affinePoint]

@[simp] theorem affinePoint_last_val
    {m a d n : ℕ} {hbound : a + d * n < m} :
    (affinePoint m a d n hbound ⟨n, Nat.lt_succ_self _⟩).1 = a + d * n := by
  simp [affinePoint]

theorem affinePoint_succ_val
    {m a d n : ℕ} {hbound : a + d * n < m}
    (s : Fin (n + 1)) (hs : s.1 + 1 < n + 1) :
    (affinePoint m a d n hbound ⟨s.1 + 1, hs⟩).1 =
      (affinePoint m a d n hbound s).1 + d := by
  simp [affinePoint, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem affinePoint_injective
    {m a d n : ℕ} {hbound : a + d * n < m} (hd : 0 < d) :
    Function.Injective (affinePoint m a d n hbound) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [affinePoint] at hv
  omega

def headAffinePoint (m head a d n : ℕ)
    (hhead : head < m) (hbound : a + d * n < m) :
    Fin (n + 1) → Fin m := fun s =>
  if _hs0 : s.1 = 0 then
    ⟨head, hhead⟩
  else
    ⟨a + d * s.1, affinePoint_bound hbound (Nat.le_of_lt_succ s.2)⟩

theorem headAffinePoint_val
    {m head a d n : ℕ} {hhead : head < m} {hbound : a + d * n < m}
    (s : Fin (n + 1)) :
    (headAffinePoint m head a d n hhead hbound s).1 =
      if s.1 = 0 then head else a + d * s.1 := by
  by_cases hs0 : s.1 = 0
  · simp [headAffinePoint, hs0]
  · simp [headAffinePoint, hs0]

@[simp] theorem headAffinePoint_zero_val
    {m head a d n : ℕ} {hhead : head < m} {hbound : a + d * n < m} :
    (headAffinePoint m head a d n hhead hbound 0).1 = head := by
  simp [headAffinePoint]

theorem headAffinePoint_injective
    {m head a d n : ℕ} {hhead : head < m} {hbound : a + d * n < m}
    (hd : 0 < d)
    (hsep : ∀ k, 0 < k → k ≤ n → head ≠ a + d * k) :
    Function.Injective (headAffinePoint m head a d n hhead hbound) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs0 : s.1 = 0
  · by_cases ht0 : t.1 = 0
    · exact Fin.ext (by omega)
    · have htPos : 0 < t.1 := Nat.pos_of_ne_zero ht0
      have htLe : t.1 ≤ n := Nat.le_of_lt_succ t.2
      have hv' : head = a + d * t.1 := by
        simpa [headAffinePoint, hs0, ht0] using hv
      exact False.elim ((hsep t.1 htPos htLe) hv')
  · by_cases ht0 : t.1 = 0
    · have hsPos : 0 < s.1 := Nat.pos_of_ne_zero hs0
      have hsLe : s.1 ≤ n := Nat.le_of_lt_succ s.2
      have hv' : a + d * s.1 = head := by
        simpa [headAffinePoint, hs0, ht0] using hv
      exact False.elim ((hsep s.1 hsPos hsLe) hv'.symm)
    · have hsEq : headAffinePoint m head a d n hhead hbound s = affinePoint m a d n hbound s := by
        apply Fin.ext
        simp [headAffinePoint, affinePoint, hs0]
      have htEq : headAffinePoint m head a d n hhead hbound t = affinePoint m a d n hbound t := by
        apply Fin.ext
        simp [headAffinePoint, affinePoint, ht0]
      have hAff : affinePoint m a d n hbound s = affinePoint m a d n hbound t := by
        calc
          affinePoint m a d n hbound s = headAffinePoint m head a d n hhead hbound s := hsEq.symm
          _ = headAffinePoint m head a d n hhead hbound t := h
          _ = affinePoint m a d n hbound t := htEq
      exact affinePoint_injective (m := m) (a := a) (d := d) (n := n) (hbound := hbound) hd hAff

def tailAffinePoint (m a d n tail : ℕ)
    (htail : tail < m) (hbound : a + d * n < m) :
    Fin (n + 1) → Fin m := fun s =>
  if _hlast : s.1 = n then
    ⟨tail, htail⟩
  else
    ⟨a + d * s.1, affinePoint_bound hbound (Nat.le_of_lt_succ s.2)⟩

theorem tailAffinePoint_val
    {m a d n tail : ℕ} {htail : tail < m} {hbound : a + d * n < m}
    (s : Fin (n + 1)) :
    (tailAffinePoint m a d n tail htail hbound s).1 =
      if s.1 = n then tail else a + d * s.1 := by
  by_cases hlast : s.1 = n
  · simp [tailAffinePoint, hlast]
  · simp [tailAffinePoint, hlast]

@[simp] theorem tailAffinePoint_last_val
    {m a d n tail : ℕ} {htail : tail < m} {hbound : a + d * n < m} :
    (tailAffinePoint m a d n tail htail hbound ⟨n, Nat.lt_succ_self _⟩).1 = tail := by
  simp [tailAffinePoint]

theorem tailAffinePoint_injective
    {m a d n tail : ℕ} {htail : tail < m} {hbound : a + d * n < m}
    (hd : 0 < d)
    (hsep : ∀ k, k < n → a + d * k ≠ tail) :
    Function.Injective (tailAffinePoint m a d n tail htail hbound) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hsLast : s.1 = n
  · by_cases htLast : t.1 = n
    · exact Fin.ext (by omega)
    · have htLt : t.1 < n := by omega
      have hv' : tail = a + d * t.1 := by
        simpa [tailAffinePoint, hsLast, htLast] using hv
      exact False.elim ((hsep t.1 htLt) hv'.symm)
  · by_cases htLast : t.1 = n
    · have hsLt : s.1 < n := by omega
      have hv' : a + d * s.1 = tail := by
        simpa [tailAffinePoint, hsLast, htLast] using hv
      exact False.elim ((hsep s.1 hsLt) hv')
    · have hsEq : tailAffinePoint m a d n tail htail hbound s = affinePoint m a d n hbound s := by
        apply Fin.ext
        simp [tailAffinePoint, affinePoint, hsLast]
      have htEq : tailAffinePoint m a d n tail htail hbound t = affinePoint m a d n hbound t := by
        apply Fin.ext
        simp [tailAffinePoint, affinePoint, htLast]
      have hAff : affinePoint m a d n hbound s = affinePoint m a d n hbound t := by
        calc
          affinePoint m a d n hbound s = tailAffinePoint m a d n tail htail hbound s := hsEq.symm
          _ = tailAffinePoint m a d n tail htail hbound t := h
          _ = affinePoint m a d n hbound t := htEq
      exact affinePoint_injective (m := m) (a := a) (d := d) (n := n) (hbound := hbound) hd hAff

private theorem headThenAffinePoint_bound
    {m a d k t : ℕ} (hbound : a + d * (k - 1) < m)
    (ht0 : t ≠ 0) (ht : t < k + 1) :
    a + d * (t - 1) < m := by
  have hpred : t - 1 ≤ k - 1 := by omega
  have hmul : d * (t - 1) ≤ d * (k - 1) := Nat.mul_le_mul_left d hpred
  omega

def headThenAffinePoint (m head a d k : ℕ)
    (hhead : head < m) (hbound : a + d * (k - 1) < m) :
    Fin (k + 1) → Fin m := fun s =>
  if hs0 : s.1 = 0 then
    ⟨head, hhead⟩
  else
    ⟨a + d * (s.1 - 1), headThenAffinePoint_bound hbound hs0 s.2⟩

theorem headThenAffinePoint_val
    {m head a d k : ℕ} {hhead : head < m} {hbound : a + d * (k - 1) < m}
    (s : Fin (k + 1)) :
    (headThenAffinePoint m head a d k hhead hbound s).1 =
      if s.1 = 0 then head else a + d * (s.1 - 1) := by
  by_cases hs0 : s.1 = 0
  · simp [headThenAffinePoint, hs0]
  · simp [headThenAffinePoint, hs0]

@[simp] theorem headThenAffinePoint_zero_val
    {m head a d k : ℕ} {hhead : head < m} {hbound : a + d * (k - 1) < m} :
    (headThenAffinePoint m head a d k hhead hbound 0).1 = head := by
  simp [headThenAffinePoint]

@[simp] theorem headThenAffinePoint_last_val
    {m head a d k : ℕ} {hhead : head < m} {hbound : a + d * (k - 1) < m}
    (hk : 0 < k) :
    (headThenAffinePoint m head a d k hhead hbound ⟨k, Nat.lt_succ_self _⟩).1 =
      a + d * (k - 1) := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp [headThenAffinePoint, hk0]

theorem headThenAffinePoint_injective
    {m head a d k : ℕ} {hhead : head < m} {hbound : a + d * (k - 1) < m}
    (hd : 0 < d)
    (hsep : ∀ j, j < k -> head ≠ a + d * j) :
    Function.Injective (headThenAffinePoint m head a d k hhead hbound) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs0 : s.1 = 0
  · by_cases ht0 : t.1 = 0
    · exact Fin.ext (by omega)
    · have htPredLt : t.1 - 1 < k := by omega
      have hv' : head = a + d * (t.1 - 1) := by
        simpa [headThenAffinePoint, hs0, ht0] using hv
      exact False.elim ((hsep (t.1 - 1) htPredLt) hv')
  · by_cases ht0 : t.1 = 0
    · have hsPredLt : s.1 - 1 < k := by omega
      have hv' : a + d * (s.1 - 1) = head := by
        simpa [headThenAffinePoint, hs0, ht0] using hv
      exact False.elim ((hsep (s.1 - 1) hsPredLt) hv'.symm)
    · apply Fin.ext
      have hv' : a + d * (s.1 - 1) = a + d * (t.1 - 1) := by
        simpa [headThenAffinePoint, hs0, ht0] using hv
      have hmulEq : d * (s.1 - 1) = d * (t.1 - 1) := Nat.add_left_cancel hv'
      have hpredEq : s.1 - 1 = t.1 - 1 := Nat.eq_of_mul_eq_mul_left hd hmulEq
      have hsPos : 0 < s.1 := Nat.pos_of_ne_zero hs0
      have htPos : 0 < t.1 := Nat.pos_of_ne_zero ht0
      omega

private theorem affineThenTailPoint_bound
    {m a d k t : ℕ} (hbound : a + d * (k - 1) < m)
    (htLast : t ≠ k) (ht : t < k + 1) :
    a + d * t < m := by
  have hlt : t < k := by omega
  have hle : t ≤ k - 1 := by omega
  have hmul : d * t ≤ d * (k - 1) := Nat.mul_le_mul_left d hle
  omega

def affineThenTailPoint (m a d k tail : ℕ)
    (htail : tail < m) (hbound : a + d * (k - 1) < m) :
    Fin (k + 1) → Fin m := fun s =>
  if hsLast : s.1 = k then
    ⟨tail, htail⟩
  else
    ⟨a + d * s.1, affineThenTailPoint_bound hbound hsLast s.2⟩

theorem affineThenTailPoint_val
    {m a d k tail : ℕ} {htail : tail < m} {hbound : a + d * (k - 1) < m}
    (s : Fin (k + 1)) :
    (affineThenTailPoint m a d k tail htail hbound s).1 =
      if s.1 = k then tail else a + d * s.1 := by
  by_cases hsLast : s.1 = k
  · simp [affineThenTailPoint, hsLast]
  · simp [affineThenTailPoint, hsLast]

@[simp] theorem affineThenTailPoint_last_val
    {m a d k tail : ℕ} {htail : tail < m} {hbound : a + d * (k - 1) < m} :
    (affineThenTailPoint m a d k tail htail hbound ⟨k, Nat.lt_succ_self _⟩).1 = tail := by
  simp [affineThenTailPoint]

theorem affineThenTailPoint_injective
    {m a d k tail : ℕ} {htail : tail < m} {hbound : a + d * (k - 1) < m}
    (hd : 0 < d)
    (hsep : ∀ j, j < k -> a + d * j ≠ tail) :
    Function.Injective (affineThenTailPoint m a d k tail htail hbound) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hsLast : s.1 = k
  · by_cases htLast : t.1 = k
    · exact Fin.ext (by omega)
    · have htLt : t.1 < k := by omega
      have hv' : tail = a + d * t.1 := by
        simpa [affineThenTailPoint, hsLast, htLast] using hv
      exact False.elim ((hsep t.1 htLt) hv'.symm)
  · by_cases htLast : t.1 = k
    · have hsLt : s.1 < k := by omega
      have hv' : a + d * s.1 = tail := by
        simpa [affineThenTailPoint, hsLast, htLast] using hv
      exact False.elim ((hsep s.1 hsLt) hv')
    · apply Fin.ext
      have hv' : a + d * s.1 = a + d * t.1 := by
        simpa [affineThenTailPoint, hsLast, htLast] using hv
      have hmulEq : d * s.1 = d * t.1 := Nat.add_left_cancel hv'
      have hsEq : s.1 = t.1 := Nat.eq_of_mul_eq_mul_left hd hmulEq
      exact hsEq

end ArithmeticBlocks

end TorusD3Even
