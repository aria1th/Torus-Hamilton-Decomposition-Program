# D7 odd Lean formalization: requested helper theorems

This note records helper theorems that would materially reduce the cost of the
Lean 4 formalization of the `D_7(m)` odd handoff bundle.

## 1. Rank-array finite cycle checker

The small cases `m=3,5` come with rank certificates.  A direct generated
pattern-match proof works for `m=3` but is too expensive to scale comfortably to
`m=5`.

The first proof-level theorem is now present in
`D7Odd/Handoff/ReturnCriterion.lean`:

```lean
theorem singleCycle_of_rankFun
    {N : Nat} [NeZero N]
    (next rank : Fin N -> Fin N)
    (hRank : Function.Bijective rank)
    (hStep : forall i, rank (next i) = rank i + 1) :
    IsSingleCycleMap next
```

The executable verifier/soundness layer is also present in
`D7Odd/Handoff/ReturnCriterion.lean`.  The Lean side now has a proof-facing
`RankArrayCert.Valid` proposition, `RankArrayCert.ok`, and
`RankArrayCert.singleCycle_of_ok`; generated rank data can therefore be checked
with `native_decide` against a boolean condition instead of expanding a
15625-state proof term.

Requested verifier shape:

```lean
structure RankArrayCert (N : Nat) where
  next : Array Nat
  rank : Array Nat
  invRank : Array Nat

def RankArrayCert.ok (C : RankArrayCert N) : Bool :=
  -- sizes are exactly N
  -- all entries are strictly < N
  -- invRank[rank[i]] = i for all i
  -- rank[invRank[r]] = r for all r
  -- rank[next[i]] = (rank[i] + 1) % N for all i
  ...

theorem RankArrayCert.singleCycle_of_ok
    {N : Nat} [NeZero N]
    (C : RankArrayCert N)
    (h : C.ok = true) :
    IsSingleCycleMap (C.nextFunOfOk h)
```

The important design constraint is that `nextFun` and `rankFun` must not silently
wrap bad entries with `% N`; the verifier establishes the bounds.  The generated
`m=3` and `m=5` rank certificates are now split across Lean modules so that the
large `m=5` tables do not create one oversized proof file.

## 2. Matrix-to-layer schedule

This theorem was part of the original matrix-generic route: turn a nonnegative
`7 x 7` integer matrix with row and column sums equal to `m` into `m`
permutation layers.

The current `D_7` Lean route uses explicit schedules for the four handoff
families, so `integer_birkhoff_fin` is no longer a blocker for this
formalization.  It remains a useful future helper if the explicit schedules are
replaced by a fully matrix-generic construction.

Conceptual theorem shape:

```lean
theorem integer_birkhoff_fin
    (A : Fin n -> Fin n -> Nat)
    (hrow : forall i, Finset.univ.sum (fun j => A i j) = m)
    (hcol : forall j, Finset.univ.sum (fun i => A i j) = m) :
    exists layers : Fin m -> Equiv.Perm (Fin n),
      forall i j,
        (Finset.univ.filter fun t => layers t i = j).card = A i j
```

With this theorem, a future version could avoid maintaining explicit symbolic
schedules for the three `m mod 6` families.

## 3. Canonical word primitiveity

The hard symbolic part of the handoff is the canonical return-map cycle
criterion.

Requested theorem shape:

```lean
theorem canonical_word_single_cycle_of_counts
    (h0 : Nat.Coprime N0 m)
    (hk : forall k, 2 <= k -> k <= q ->
      Nat.Coprime
        (Int.natAbs (Int.ofNat (Nk k) - Int.ofNat NDelta))
        m) :
    IsSingleCycleMap (canonicalReturn W)
```

The `Int.ofNat` casts are intentional: using `Nat` subtraction here would
truncate.  This should be proved once by the skew-product/carry calculation
described in the handoff note.

In the current `D_7` Lean files, the exact requested theorem is the q=6
word-level rank form recorded later as
`CanonicalPrefixWordReturnRankTheorem`.  Its hypothesis is
`CanonicalWordCertified m W`, which packages the same coprime count conditions
through `canonicalRowPrimitive`.

## 4. Count-matrix glue

The row/column sum and row primitive/unit arithmetic for the four handoff
matrices is now present in
`D7Odd/Handoff/CanonicalCountMatrices.lean`:

```lean
theorem matrix7_valid : CountMatrixValid 7 matrix7

theorem matrix7_primitive : CountMatrixPrimitive 7 matrix7

theorem matrix7_certified : CountMatrixCertified 7 matrix7

theorem matrix6s1_valid (s : Nat) : Matrix6s1ValidTarget s

theorem matrix6s1_primitive (s : Nat) : Matrix6s1PrimitiveTarget s

theorem matrix6s1_certified (s : Nat) : Matrix6s1CertifiedTarget s

theorem matrix6s3_valid (s : Nat) : Matrix6s3ValidTarget s

theorem matrix6s3_primitive (s : Nat) : Matrix6s3PrimitiveTarget s

theorem matrix6s3_certified (s : Nat) : Matrix6s3CertifiedTarget s

theorem matrix6s5_valid (s : Nat) : Matrix6s5ValidTarget s

theorem matrix6s5_primitive (s : Nat) : Matrix6s5PrimitiveTarget s

theorem matrix6s5_certified (s : Nat) : Matrix6s5CertifiedTarget s

theorem generic_count_matrix_certified {m : Nat}
    (hm7 : 7 <= m) (hodd : Odd m) :
    GenericCountMatrixCertified m
```

The matrix arithmetic is now connected to the current generic construction by an
explicit schedule route.  Consequently the specific `D_7` branch no longer has
to depend on `integer_birkhoff_fin`; that theorem is only useful for a future
matrix-generic route.  The canonical return-map cycle theorem is now supplied
by `D7Odd/Handoff/CanonicalFamily.lean`.

`D7Odd/Handoff/CanonicalSchedules.lean` contains fixed base schedules and a
six-layer increment block:

```lean
theorem canonicalSchedule6s1_latin (s : Nat) :
    scheduleListLatin (canonicalSchedule6s1 s)

theorem canonicalSchedule6s1_length (s : Nat) (hs : 2 <= s) :
    (canonicalSchedule6s1 s).length = 6*s + 1

theorem canonicalSchedule6s1_count (s : Nat) (hs : 2 <= s) :
    forall c sym : Fin 7,
      scheduleCount (canonicalSchedule6s1 s) c sym = matrix6s1 s c sym

-- and analogous theorems for `6s+3` and `6s+5`
```

The schedules are now packaged with their certified count matrices:

```lean
structure CountMatrixSchedule (m : Nat) where
  matrix : CountMatrix
  schedule : List SymbolPerm7
  certified : CountMatrixCertified m matrix
  latin : scheduleListLatin schedule
  length_eq : schedule.length = m
  count_eq : forall c sym : Fin 7, scheduleCount schedule c sym = matrix c sym

theorem generic_count_matrix_schedule {m : Nat}
    (hm7 : 7 <= m) (hodd : Odd m) :
    Nonempty (CountMatrixSchedule m)
```

`D7Odd/Handoff/CanonicalWords.lean` now turns each row of a certified schedule
into the word-level primitiveity input required by the canonical return theorem:

```lean
def CanonicalWordCertified (m : Nat) (W : List CanonSym) : Prop :=
  W.length = m ∧ canonicalRowPrimitive m (fun sym => canonicalWordCount W sym)

theorem countMatrixSchedule_word_certified {m : Nat}
    (P : CountMatrixSchedule m) (c : Fin 7) :
    CanonicalWordCertified m (canonicalWord P.schedule c)

theorem generic_canonical_words_certified {m : Nat}
    (hm7 : 7 <= m) (hodd : Odd m) :
    GenericCanonicalWordsCertified m
```

The generic realization theorem is isolated in
`D7Odd/Handoff/CanonicalBridge.lean`:

```lean
structure CanonicalScheduleRealization (m : Nat) [NeZero m]
    (P : CountMatrixSchedule m) where
  schedule : RootFlatSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle :
    (forall c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) ->
      schedule.returnsSingleCycle

def CanonicalScheduleRealizationTheorem : Prop :=
  forall {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    Nonempty (CanonicalScheduleRealization m P)

def CanonicalScheduleHamiltonianTheorem : Prop :=
  forall {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    (forall c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) ->
      HamiltonDecompositionD7 m

theorem generic_odd_from_canonical_schedule
    (hcanonical : CanonicalScheduleHamiltonianTheorem) :
    GenericOddBranchResult

theorem main_odd_from_canonical_schedule
    (hcanonical : CanonicalScheduleHamiltonianTheorem) :
    MainOddTheoremTarget

theorem generic_odd_from_canonical_realization
    (hrealize : CanonicalScheduleRealizationTheorem) :
    GenericOddBranchResult
```

`D7Odd/Handoff/CanonicalFamily.lean` now defines the concrete canonical
root-flat schedule associated to a `CountMatrixSchedule`:

```lean
def rootPrefixCoord {m : Nat} (w : RootState7 m) : Fin 6 -> ZMod m

def canonicalRho {m : Nat} (t : ZMod m) (w : RootState7 m) : Rho6

def canonicalLayerDir {m : Nat}
    (t : ZMod m) (w : RootState7 m) (sym : CanonSym) : Direction

def canonicalRootFlatSchedule {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) : RootFlatSchedule m

theorem canonicalRootFlatSchedule_rowLatin {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) :
    (canonicalRootFlatSchedule P).rowLatin
```

The row-Latin part is therefore closed.  The file also defines and proves the
root-prefix coordinate equivalence and the direction/coordinate compatibility:

```lean
def rootOfPrefix {m : Nat} (z : Fin 6 -> ZMod m) : RootState7 m

theorem rootPrefixCoord_bijective {m : Nat} :
    Function.Bijective (rootPrefixCoord : RootState7 m -> Fin 6 -> ZMod m)

theorem rootPrefixCoord_addQRoot_prefixLabel {m : Nat}
    (r : Fin 7) (w : RootState7 m) :
    rootPrefixCoord (addQRoot m (prefixLabelToDirection r) w) =
      prefixLabelStep r (rootPrefixCoord w)

theorem rootPrefixCoord_subQRoot_prefixLabel {m : Nat}
    (r : Fin 7) (w : RootState7 m) :
    rootPrefixCoord (subQRoot m (prefixLabelToDirection r) w) =
      prefixLabelUnstep r (rootPrefixCoord w)
```

The layer-bijection work has been reduced to, and then discharged through,
concrete inverse identities for the prefix map:

```lean
def canonicalPrefixInvMap {m : Nat}
    (t : ZMod m) (sym : CanonSym) :
    (Fin 6 -> ZMod m) -> (Fin 6 -> ZMod m)

def CanonicalPrefixLayerInverseTheorem : Prop :=
  forall {m : Nat} [NeZero m] (t : ZMod m) (sym : CanonSym),
    (forall z, canonicalPrefixInvMap t sym (canonicalPrefixMap t sym z) = z) ∧
      (forall z, canonicalPrefixMap t sym (canonicalPrefixInvMap t sym z) = z)

theorem canonicalLayerBijective_of_prefix_inverse
    (hinv : CanonicalPrefixLayerInverseTheorem) :
    CanonicalLayerBijectiveTheorem

theorem canonicalPrefixLayerInverse : CanonicalPrefixLayerInverseTheorem

theorem canonicalLayerBijective : CanonicalLayerBijectiveTheorem
```

The inverse theorem is discharged in Lean by splitting all seven symbols:

```lean
theorem canonicalPrefixLayerInverse_zero {m : Nat} [NeZero m] (t : ZMod m) :
    (forall z, canonicalPrefixInvMap t 0 (canonicalPrefixMap t 0 z) = z) ∧
      (forall z, canonicalPrefixMap t 0 (canonicalPrefixInvMap t 0 z) = z)

theorem canonicalPrefixLayerInverse_delta {m : Nat} [NeZero m] (t : ZMod m) :
    (forall z, canonicalPrefixInvMap t 1 (canonicalPrefixMap t 1 z) = z) ∧
      (forall z, canonicalPrefixMap t 1 (canonicalPrefixInvMap t 1 z) = z)

theorem canonicalPrefixLayerInverse_two {m : Nat} [NeZero m] (t : ZMod m) :
    (forall z, canonicalPrefixInvMap t 2 (canonicalPrefixMap t 2 z) = z) ∧
      (forall z, canonicalPrefixMap t 2 (canonicalPrefixInvMap t 2 z) = z)

-- and analogous theorems for symbols `3`, `4`, `5`, and `6`
```

The file also contains finite support lemmas such as
`exists_fin6_lt_two_eq` through `exists_fin6_lt_five_eq` for expanding the
“some earlier coordinate” inverse branch.

The return single-cycle theorem has been reduced from root-flat states to the
prefix-coordinate return and is now closed by the recursive canonical-family
proof in `D7Odd/Handoff/CanonicalFamily.lean`:

```lean
def canonicalPrefixScheduleReturn {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) :
    (Fin 6 -> ZMod m) -> (Fin 6 -> ZMod m)

theorem rootPrefixCoord_canonicalPrefixScheduleReturn {m : Nat} [NeZero m]
    (P : CountMatrixSchedule m) (c : Fin 7) (w : RootState7 m) :
    rootPrefixCoord ((canonicalRootFlatSchedule P).returnMap c w) =
      canonicalPrefixScheduleReturn P c (rootPrefixCoord w)

def CanonicalPrefixReturnSingleCycleTheorem : Prop :=
  forall {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    (forall c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) ->
      forall c : Fin 7, IsSingleCycleMap (canonicalPrefixScheduleReturn P c)
```

The schedule-specific statement has now been lowered one more step to a
word-level theorem.  `canonicalPrefixWordAt` reads the symbol at layer `t.val`
when it is within the word, and `canonicalPrefixWordReturn` folds the same
canonical prefix maps over `List.range m`:

```lean
def canonicalPrefixWordAt {m : Nat} (W : List CanonSym) (t : ZMod m) :
    CanonSym

def canonicalPrefixWordReturn {m : Nat} [NeZero m] (W : List CanonSym) :
    (Fin 6 -> ZMod m) -> (Fin 6 -> ZMod m)

def CanonicalPrefixWordSingleCycleTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      IsSingleCycleMap (canonicalPrefixWordReturn (m := m) W)

theorem canonicalPrefixReturnSingleCycle_of_word
    (hword : CanonicalPrefixWordSingleCycleTheorem) :
    CanonicalPrefixReturnSingleCycleTheorem
```

The earlier proof-friendly request was the rank-step form below: a monolithic
way to prove the skew/carry primitiveity calculation by producing a global rank
on `(ZMod m)^6`.  The implemented proof instead uses recursive fibers.

```lean
def CanonicalPrefixWordReturnRankTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      exists rank : ((Fin 6 -> ZMod m) -> ZMod (m ^ 6)),
        Function.Bijective rank ∧
          forall z,
            rank (canonicalPrefixWordReturn (m := m) W z) = rank z + 1

theorem canonicalPrefixWordSingleCycle_of_rank
    (hrank : CanonicalPrefixWordReturnRankTheorem) :
    CanonicalPrefixWordSingleCycleTheorem

theorem canonical_realization_theorem_of_word_rank
    (hrank : CanonicalPrefixWordReturnRankTheorem) :
    CanonicalScheduleRealizationTheorem

theorem main_odd_from_canonical_word_rank
    (hrank : CanonicalPrefixWordReturnRankTheorem) :
    MainOddTheoremTarget
```

Recommended proof split for `CanonicalPrefixWordReturnRankTheorem`:

1. Prove a q=6 carry-normal-form lemma for `canonicalPrefixWordReturn`.  The
   normal form should depend only on the counts
   `canonicalWordCount W 0`, `canonicalWordCount W 1`, and
   `canonicalWordCount W k` for `2 <= k`.
2. Prove the skew/carry rank lemma for that normal form.  The rank target should
   be `ZMod (m ^ 6)`, and the step equation should be exactly
   `rank (F z) = rank z + 1`.
3. Use `CanonicalWordCertified m W` only at the final arithmetic step, where it
   supplies `Nat.Coprime (canonicalWordCount W 0) m` and
   `Nat.Coprime (Int.natAbs (...)) m` for the differences
   `canonicalWordCount W k - canonicalWordCount W 1`.

This split keeps the count-matrix and explicit-schedule files out of the proof;
they already discharge `CanonicalWordCertified` for every row.

### 3.1 Current q=6 recursive head-drift shape

The recursive fiber route is now sign-aligned with the handoff bundle's carry
calculation.  The actual head drifts for the peeled coordinates alternate by
the factor `(m - 1)^r`:

```lean
-- proved
CanonicalPrefixWordFiberHeadDriftTheorem
-- drift: +(N_delta - N_2)

-- proved
CanonicalPrefixWordSubfiberHeadDriftTheorem
-- drift: -(N_delta - N_3)

-- proved
CanonicalPrefixWordSubsubfiberHeadDriftTheorem
-- drift: +(N_delta - N_4)

-- proved
CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem
-- drift: -(N_delta - N_5)

-- proved
CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem
-- drift: +(N_delta - N_6)
```

The k=3 through k=6 recursive head drifts are now proved in
`D7Odd/Handoff/CanonicalFamily.lean`.  The k=3 proof uses the two-coordinate
orbit hit theorem below:

```lean
def CanonicalPrefixWordSubfiberDebitTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (b0 b1 : ZMod m) (tail : Fin 4 -> ZMod m),
        canonicalPrefixWordReturnIterDebitTwo W
          (prefixFiberBase b0 (tail5FiberBase b1 tail)) (m * m) =
            (canonicalWordDeltaDrift W (3 : Fin 7) : ZMod m)

theorem canonicalPrefixWordSubfiberHeadDrift_of_debit
    (hdebit : CanonicalPrefixWordSubfiberDebitTheorem) :
    CanonicalPrefixWordSubfiberHeadDriftTheorem
```

This is the q=2 instance of the carry-count statement: over one full lower
orbit, the indicator that at least one lower coordinate is at the current layer
has modular sum `-1`, so the coordinate-2 debit is `N_delta - N_3`.

The current Lean file reduces that debit identity one step further to the
following hit-count theorem:

```lean
def canonicalPrefixWordLayerHitTwo {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 -> ZMod m) (j t : Nat) : Prop :=
  canonicalPrefixCoordTwoHit (t : ZMod m)
    (canonicalPrefixWordPrefixState W t
      ((canonicalPrefixWordReturn (m := m) W)^[j] z))

def CanonicalPrefixWordLayerHitTwoSumTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (z : Fin 6 -> ZMod m) (t : Nat),
        Finset.sum (Finset.range (m * m))
          (fun j : Nat =>
            if canonicalPrefixWordLayerHitTwo W z j t then (1 : ZMod m) else 0) =
          -1

theorem canonicalPrefixWordSubfiberDebit_of_hit_two_sum
    (hhitTwo : CanonicalPrefixWordLayerHitTwoSumTheorem) :
    CanonicalPrefixWordSubfiberDebitTheorem

theorem canonicalPrefixWordSubfiberHeadDrift_of_hit_two_sum
    (hhitTwo : CanonicalPrefixWordLayerHitTwoSumTheorem) :
    CanonicalPrefixWordSubfiberHeadDriftTheorem

theorem canonicalPrefixWordLayerHitTwoSum :
    CanonicalPrefixWordLayerHitTwoSumTheorem

theorem canonicalPrefixWordSubfiberHeadDrift :
    CanonicalPrefixWordSubfiberHeadDriftTheorem
```

The k=4 proof uses the analogous three-coordinate orbit theorem:

```lean
def CanonicalPrefixWordLayerHitThreeSumTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (z : Fin 6 -> ZMod m) (t : Nat),
        Finset.sum (Finset.range (m * m * m))
          (fun j : Nat =>
            if canonicalPrefixWordLayerHitThree W z j t then (1 : ZMod m) else 0) =
          1

theorem canonicalPrefixWordLayerHitThreeSum :
    CanonicalPrefixWordLayerHitThreeSumTheorem

theorem canonicalPrefixWordSubsubfiberHeadDrift :
    CanonicalPrefixWordSubsubfiberHeadDriftTheorem
```

The same construction is now implemented for four and five lower coordinates:
`CanonicalPrefixWordLayerHitFourSumTheorem` has modular hit sum `-1`, and
`CanonicalPrefixWordLayerHitFiveSumTheorem` has modular hit sum `+1`.  These
close `canonicalPrefixWordSubsubsubfiberHeadDrift` and
`canonicalPrefixWordSubsubsubsubfiberHeadDrift`, which are packaged as
`canonicalPrefixWordRemainingHeadDrifts`.

The first-coordinate base drift is now proved in Lean:

```lean
def prefixHead {m : Nat} (z : Fin 6 -> ZMod m) : ZMod m

def prefixTail {m : Nat} (z : Fin 6 -> ZMod m) : Fin 5 -> ZMod m

def prefixSplitEquiv (m : Nat) :
    (Fin 6 -> ZMod m) ≃ ZMod m × (Fin 5 -> ZMod m)

def prefixFiberBase {m : Nat} (b : ZMod m) (tail : Fin 5 -> ZMod m) :
    Fin 6 -> ZMod m

theorem prefixFiberBase_surj {m : Nat} (b : ZMod m) :
    forall z : Fin 6 -> ZMod m, prefixHead z = b ->
      exists tail : Fin 5 -> ZMod m, prefixFiberBase b tail = z

theorem canonicalPrefixWordReturn_coord_zero {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (z : Fin 6 -> ZMod m) :
    canonicalPrefixWordReturn (m := m) W z 0 =
      z 0 + (canonicalWordCount W 0 : ZMod m)

theorem canonicalPrefixWordReturn_head {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (z : Fin 6 -> ZMod m) :
    prefixHead (canonicalPrefixWordReturn (m := m) W z) =
      prefixHead z + (canonicalWordCount W 0 : ZMod m)

theorem canonicalPrefixWordReturn_base_single_cycle {m : Nat} [NeZero m]
    {W : List CanonSym} (hW : CanonicalWordCertified m W) :
    IsSingleCycleMap
      (fun x : ZMod m => x + (canonicalWordCount W 0 : ZMod m))

theorem canonicalPrefixWordReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) :
    Function.Bijective (canonicalPrefixWordReturn (m := m) W)

def canonicalPrefixWordFiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b : ZMod m) :
    (Fin 5 -> ZMod m) -> (Fin 5 -> ZMod m)

theorem canonicalPrefixWordReturn_iter_m_fiber {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (b : ZMod m)
    (tail : Fin 5 -> ZMod m) :
    (canonicalPrefixWordReturn (m := m) W)^[m] (prefixFiberBase b tail) =
      prefixFiberBase b (canonicalPrefixWordFiberReturn W b tail)

theorem canonicalPrefixWordFiberReturn_bijective {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (b : ZMod m) :
    Function.Bijective (canonicalPrefixWordFiberReturn W b)

def CanonicalPrefixWordFiberHeadDriftTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (b : ZMod m) (tail : Fin 5 -> ZMod m),
        (canonicalPrefixWordFiberReturn W b tail) 0 =
          tail 0 + (canonicalWordDeltaTwoDrift W : ZMod m)

def canonicalPrefixWordSubfiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b0 b1 : ZMod m) :
    (Fin 4 -> ZMod m) -> (Fin 4 -> ZMod m)

def CanonicalPrefixWordSubfiberSingleCycleTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall b0 b1 : ZMod m, IsSingleCycleMap
        (canonicalPrefixWordSubfiberReturn W b0 b1)

theorem canonicalPrefixWordFiberSingleCycle_of_head_drift_subfiber
    (hhead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsub : CanonicalPrefixWordSubfiberSingleCycleTheorem) :
    CanonicalPrefixWordFiberSingleCycleTheorem

theorem canonicalPrefixWordSingleCycle_of_fiber_return {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (b₀ : ZMod m) (fiberNext : (Fin 5 -> ZMod m) -> (Fin 5 -> ZMod m))
    (returnTime : Nat)
    (hreturn : forall tail : Fin 5 -> ZMod m,
      (canonicalPrefixWordReturn (m := m) W)^[returnTime] (prefixFiberBase b₀ tail) =
        prefixFiberBase b₀ (fiberNext tail))
    (hfiber : IsSingleCycleMap fiberNext) :
    IsSingleCycleMap (canonicalPrefixWordReturn (m := m) W)

theorem canonicalPrefixWordSingleCycle_of_fiber_return_m {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W) (b₀ : ZMod m)
    (hfiber : IsSingleCycleMap (canonicalPrefixWordFiberReturn W b₀)) :
    IsSingleCycleMap (canonicalPrefixWordReturn (m := m) W)

def CanonicalPrefixWordFiberSingleCycleTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall b : ZMod m, IsSingleCycleMap (canonicalPrefixWordFiberReturn W b)

theorem canonicalPrefixWordSingleCycle_of_fiber
    (hfiber : CanonicalPrefixWordFiberSingleCycleTheorem) :
    CanonicalPrefixWordSingleCycleTheorem

theorem canonical_realization_theorem_of_fiber
    (hfiber : CanonicalPrefixWordFiberSingleCycleTheorem) :
    CanonicalScheduleRealizationTheorem

theorem main_odd_from_canonical_fiber
    (hfiber : CanonicalPrefixWordFiberSingleCycleTheorem) :
    MainOddTheoremTarget
```

Together with `CanonicalWordCertified m W`, this gives the primitive base
translation required at the first step of the skew-product proof.  The
`Subfiber` theorem now packages the next recursive split: once the first fiber
head drift is proved and the induced `Fin 4 -> ZMod m` subfiber return is known
single-cycle, the full `Fin 5 -> ZMod m` fiber theorem follows by the already
ported `single_cycle_of_fiber_return`.

The next base drift after passing to the first fiber is also packaged:

```lean
def canonicalWordDeltaTwoDrift (W : List CanonSym) : Int :=
  Int.ofNat (canonicalWordCount W 1) - Int.ofNat (canonicalWordCount W 2)

theorem canonicalWordDeltaTwoDrift_single_cycle {m : Nat} [NeZero m]
    {W : List CanonSym} (hW : CanonicalWordCertified m W) :
    IsSingleCycleMap
      (fun x : ZMod m => x + (canonicalWordDeltaTwoDrift W : ZMod m))
```

This is the `N_delta - N_2` primitive rotation supplied by
`CanonicalWordCertified.coprime_diff` at `k = 2`.

The local coordinate-one update is also proved and is the direct input for
`CanonicalPrefixWordFiberHeadDriftTheorem`:

```lean
theorem canonicalPrefixMap_coord_one {m : Nat} (t : ZMod m) (sym : CanonSym)
    (z : Fin 6 -> ZMod m) :
    canonicalPrefixMap t sym z 1 =
      z 1 -
        if sym = 0 then 0
        else if sym = 1 then if z 0 = t then 0 else 1
        else if sym = 2 then if z 0 = t then 1 else 0
        else 1
```

The first required modular counting lemma is now proved:

```lean
theorem zmod_affine_range_countP_eq_one
    {m a : Nat} [NeZero m] (ha : Nat.Coprime a m)
    (offset target : ZMod m) :
    (List.range m).countP
        (fun j : Nat => decide
          (offset + (j : ZMod m) * (a : ZMod m) = target)) = 1

theorem zmod_sum_range_indicator_eq_countP
    {m : Nat} [NeZero m] (p : Nat -> Prop) [DecidablePred p] :
    (Finset.sum (Finset.range m)
      (fun j : Nat => if p j then (1 : ZMod m) else 0)) =
      ((List.range m).countP (fun j : Nat => decide (p j)) : ZMod m)

theorem canonicalPrefixWordReturn_prefix_head_after_iter {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : W.length = m) (j t : Nat)
    (z : Fin 6 -> ZMod m) :
    ((List.range t).foldl
        (fun x (s : Nat) =>
          canonicalPrefixMap (s : ZMod m) (canonicalPrefixWordAt W (s : ZMod m)) x)
        ((canonicalPrefixWordReturn (m := m) W)^[j] z)) 0 =
      z 0 + (j : ZMod m) * (canonicalWordCount W 0 : ZMod m) -
        ((List.range t).countP
          (fun s : Nat => canonicalPrefixWordAt W (s : ZMod m) != 0) : ZMod m)

theorem canonicalPrefixWordReturn_layer_hit_count_eq_one {m : Nat} [NeZero m]
    (W : List CanonSym) (hW : CanonicalWordCertified m W)
    (z : Fin 6 -> ZMod m) (t : Nat) :
    (List.range m).countP
        (fun j : Nat => decide
          (((List.range t).foldl
              (fun x (s : Nat) =>
                canonicalPrefixMap (s : ZMod m) (canonicalPrefixWordAt W (s : ZMod m)) x)
              ((canonicalPrefixWordReturn (m := m) W)^[j] z)) 0 = (t : ZMod m))) = 1
```

This closes the “head visits each layer exactly once across `m` word-return
iterations” part of the first fiber drift proof.  The coordinate-one fold has
also been packaged as an explicit debit sum:

```lean
def canonicalPrefixCoordOneDebit {m : Nat}
    (t : ZMod m) (sym : CanonSym) (z : Fin 6 -> ZMod m) : ZMod m

def canonicalPrefixWordReturnIterDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (z : Fin 6 -> ZMod m) (n : Nat) : ZMod m

theorem canonicalPrefixWordReturn_iter_coord_one_sum {m : Nat} [NeZero m]
    (W : List CanonSym) :
    forall n : Nat, forall z : Fin 6 -> ZMod m,
      ((canonicalPrefixWordReturn (m := m) W)^[n] z) 1 =
        z 1 - canonicalPrefixWordReturnIterDebit W z n

theorem canonicalPrefixWordFiberReturn_coord_zero_of_iterDebit {m : Nat} [NeZero m]
    (W : List CanonSym) (b : ZMod m) (tail : Fin 5 -> ZMod m) :
    (canonicalPrefixWordFiberReturn W b tail) 0 =
      tail 0 - canonicalPrefixWordReturnIterDebit W (prefixFiberBase b tail) m

def CanonicalPrefixWordFiberDebitTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (b : ZMod m) (tail : Fin 5 -> ZMod m),
        canonicalPrefixWordReturnIterDebit W (prefixFiberBase b tail) m =
          - (canonicalWordDeltaTwoDrift W : ZMod m)

theorem canonicalPrefixWordFiberDebit :
    CanonicalPrefixWordFiberDebitTheorem

theorem canonicalPrefixWordFiberHeadDrift_of_debit
    (hdebit : CanonicalPrefixWordFiberDebitTheorem) :
    CanonicalPrefixWordFiberHeadDriftTheorem

theorem canonicalPrefixWordFiberHeadDrift :
    CanonicalPrefixWordFiberHeadDriftTheorem
```

The first fiber drift and all subsequent recursive drift layers are now proved.
The same calculation on `canonicalPrefixWordSubfiberReturn W b0 b1` gives the
next primitive drift `N_delta - N_3` with the sign conventions recorded above.

The structural reducer for that next layer is also in place:

```lean
def canonicalWordDeltaDrift (W : List CanonSym) (k : CanonSym) : Int :=
  Int.ofNat (canonicalWordCount W 1) - Int.ofNat (canonicalWordCount W k)

theorem canonicalWordDeltaDrift_single_cycle {m : Nat} [NeZero m]
    {W : List CanonSym} (hW : CanonicalWordCertified m W)
    (k : CanonSym) (hk : 2 <= k.val) :
    IsSingleCycleMap
      (fun x : ZMod m => x + (canonicalWordDeltaDrift W k : ZMod m))

def CanonicalPrefixWordSubfiberHeadDriftTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (b0 b1 : ZMod m) (tail : Fin 4 -> ZMod m),
        (canonicalPrefixWordSubfiberReturn W b0 b1 tail) 0 =
          tail 0 + (-(canonicalWordDeltaDrift W (3 : Fin 7)) : ZMod m)

def canonicalPrefixWordSubsubfiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b0 b1 b2 : ZMod m) :
    (Fin 3 -> ZMod m) -> (Fin 3 -> ZMod m)

def CanonicalPrefixWordSubsubfiberSingleCycleTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall b0 b1 b2 : ZMod m, IsSingleCycleMap
        (canonicalPrefixWordSubsubfiberReturn W b0 b1 b2)

theorem canonicalPrefixWordSubfiberSingleCycle_of_head_drift_subsubfiber
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    (hsubsub : CanonicalPrefixWordSubsubfiberSingleCycleTheorem) :
    CanonicalPrefixWordSubfiberSingleCycleTheorem

def CanonicalPrefixWordSubsubfiberHeadDriftTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (b0 b1 b2 : ZMod m) (tail : Fin 3 -> ZMod m),
        (canonicalPrefixWordSubsubfiberReturn W b0 b1 b2 tail) 0 =
          tail 0 + (canonicalWordDeltaDrift W (4 : Fin 7) : ZMod m)

def canonicalPrefixWordSubsubsubfiberReturn {m : Nat} [NeZero m]
    (W : List CanonSym) (b0 b1 b2 b3 : ZMod m) :
    (Fin 2 -> ZMod m) -> (Fin 2 -> ZMod m)

def CanonicalPrefixWordSubsubsubfiberSingleCycleTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall b0 b1 b2 b3 : ZMod m, IsSingleCycleMap
        (canonicalPrefixWordSubsubsubfiberReturn W b0 b1 b2 b3)

theorem canonicalPrefixWordSubsubfiberSingleCycle_of_head_drift_subsubsubfiber
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    (hsubsubHead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    (hsubsubsub : CanonicalPrefixWordSubsubsubfiberSingleCycleTheorem) :
    CanonicalPrefixWordSubsubfiberSingleCycleTheorem

def CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (b0 b1 b2 b3 : ZMod m) (tail : Fin 2 -> ZMod m),
        (canonicalPrefixWordSubsubsubfiberReturn W b0 b1 b2 b3 tail) 0 =
          tail 0 + (-(canonicalWordDeltaDrift W (5 : Fin 7)) : ZMod m)

def CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem : Prop :=
  forall {m : Nat} [NeZero m] (W : List CanonSym),
    CanonicalWordCertified m W ->
      forall (b0 b1 b2 b3 b4 : ZMod m) (tail : Fin 1 -> ZMod m),
        (canonicalPrefixWordSubsubsubsubfiberReturn W b0 b1 b2 b3 b4 tail) 0 =
          tail 0 + (canonicalWordDeltaDrift W (6 : Fin 7) : ZMod m)

theorem canonicalPrefixWordSubsubsubfiberSingleCycle_of_head_drift_subsubsubsubfiber
    (hfiberHead : CanonicalPrefixWordFiberHeadDriftTheorem)
    (hsubHead : CanonicalPrefixWordSubfiberHeadDriftTheorem)
    (hsubsubHead : CanonicalPrefixWordSubsubfiberHeadDriftTheorem)
    (hsubsubsubHead : CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem)
    (hsubsubsubsub : CanonicalPrefixWordSubsubsubsubfiberSingleCycleTheorem) :
    CanonicalPrefixWordSubsubsubfiberSingleCycleTheorem

theorem canonicalPrefixWordSubsubsubsubfiberSingleCycle_of_head_drift
    (hhead : CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem) :
    CanonicalPrefixWordSubsubsubsubfiberSingleCycleTheorem

def CanonicalPrefixWordRemainingHeadDriftsTheorem : Prop :=
  CanonicalPrefixWordSubfiberHeadDriftTheorem /\
    CanonicalPrefixWordSubsubfiberHeadDriftTheorem /\
      CanonicalPrefixWordSubsubsubfiberHeadDriftTheorem /\
        CanonicalPrefixWordSubsubsubsubfiberHeadDriftTheorem

theorem main_odd_from_canonical_remaining_head_drifts
    (hheads : CanonicalPrefixWordRemainingHeadDriftsTheorem) :
    MainOddTheoremTarget
```

This is the layer-level calculation needed to identify the first coordinate of
`canonicalPrefixWordFiberReturn W b` with the `N_delta - N_2` drift.

The reusable rotation lemma behind this is also present in
`D7Odd/Handoff/ReturnCriterion.lean`:

```lean
theorem zmod_add_single_cycle_of_coprime
    {m a : Nat} [NeZero m] (ha : Nat.Coprime a m) :
    IsSingleCycleMap (fun x : ZMod m => x + (a : ZMod m))

theorem zmod_int_add_single_cycle_of_coprime_abs
    {m : Nat} [NeZero m] (a : Int) (ha : Nat.Coprime a.natAbs m) :
    IsSingleCycleMap (fun x : ZMod m => x + (a : ZMod m))
```

The D5-style return-cover reducer has also been ported to
`D7Odd/Handoff/ReturnCriterion.lean`:

```lean
theorem single_cycle_of_return_cover
    {α σ : Type*} (f : α -> α) (base : σ -> α)
    (next : σ -> σ) (time : σ -> Nat)
    (hf : Function.Bijective f)
    (hreturn : forall s : σ, f^[time s] (base s) = base (next s))
    (hcover : forall x : α, exists s : σ, exists k : Nat,
      k < time s ∧ f^[k] (base s) = x)
    (hnext : IsSingleCycleMap next) :
    IsSingleCycleMap f

theorem single_cycle_of_first_return_sum
    {α σ : Type*} [Fintype α] [Fintype σ]
    (f : α -> α) (base : σ -> α)
    (next : σ -> σ) (time : σ -> Nat)
    (hf : Function.Bijective f)
    (hbase_inj : Function.Injective base)
    (hreturn : forall s : σ, f^[time s] (base s) = base (next s))
    (hfirst : forall s : σ, forall k : Nat, 0 < k -> k < time s ->
      ¬ exists t : σ, f^[k] (base s) = base t)
    (hnext : IsSingleCycleMap next)
    (hsum : (Finset.univ.sum fun s : σ => time s) = Fintype.card α) :
    IsSingleCycleMap f

theorem single_cycle_of_fiber_return
    {α β σ : Type*} (f : α -> α) (g : β -> β) (proj : α -> β)
    (fiberBase : σ -> α) (fiberNext : σ -> σ) (returnTime : Nat) (b₀ : β)
    (hf : Function.Bijective f)
    (hcomm : forall x : α, proj (f x) = g (proj x))
    (hfiber_surj : forall x : α, proj x = b₀ -> exists s : σ, fiberBase s = x)
    (hreturn : forall s : σ, f^[returnTime] (fiberBase s) = fiberBase (fiberNext s))
    (hbase : IsSingleCycleMap g)
    (hfiber : IsSingleCycleMap fiberNext) :
    IsSingleCycleMap f
```

The implemented route uses this recursive fiber decomposition rather than a
monolithic rank.  The closed artifacts are:

```lean
theorem canonicalPrefixWordRemainingHeadDrifts :
    CanonicalPrefixWordRemainingHeadDriftsTheorem

theorem canonicalPrefixWordSingleCycle :
    CanonicalPrefixWordSingleCycleTheorem

theorem canonical_realization_theorem :
    CanonicalScheduleRealizationTheorem

theorem main_odd :
    MainOddTheoremTarget
```

```lean

theorem canonicalReturnSingleCycle_of_prefix
    (hprefix : CanonicalPrefixReturnSingleCycleTheorem) :
    CanonicalReturnSingleCycleTheorem

def CanonicalReturnSingleCycleTheorem : Prop :=
  forall {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    (forall c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) ->
      (canonicalRootFlatSchedule P).returnsSingleCycle

theorem canonical_realization_theorem_of_return
    (hreturn : CanonicalReturnSingleCycleTheorem) :
    CanonicalScheduleRealizationTheorem
```

For a future matrix-generic route, after `integer_birkhoff_fin` and the
canonical word theorem exist, the generic branch can also be reduced to matrix
arithmetic by adding one glue theorem:

```lean
theorem canonical_schedule_from_count_matrix
    {m : Nat} [NeZero m]
    (A : Fin 7 -> CanonSym 6 -> Nat)
    (hrow : forall c, Finset.univ.sum (fun s => A c s) = m)
    (hcol : forall s, Finset.univ.sum (fun c => A c s) = m)
    (hUnits : forall c, canonicalRowPrimitive m (A c)) :
    exists schedule : Fin m -> Equiv.Perm (CanonSym 6),
      forall c, IsSingleCycleMap (canonicalReturn (wordOfSchedule schedule c))
```

This isolates the four handoff matrices (`m = 7`, `6s+1`, `6s+3`, `6s+5`) from
the schedule construction proof.

## 5. Finite map inverse checker

The `m=5` return cycles are now certified by rank arrays, and the non-selector
layers are bijective by the explicit `addQRoot`/`subQRoot` inverse.  The last
small-case bottleneck was selector-layer bijectivity:

```lean
def SmallLayer5SelectorBijectiveTarget : Prop :=
  forall c, Function.Bijective (smallLayer5 1 c)
```

A direct `native_decide` proof of `Function.Bijective` over the `5^6` root
states is too expensive.  The implemented solution uses the inverse-table bridge
now present as
`FinMapArrayCert` in `D7Odd/Handoff/ReturnCriterion.lean`:

```lean
structure FinMapArrayCert (N : Nat) where
  map : Array Nat
  inv : Array Nat

def FinMapArrayCert.ok (C : FinMapArrayCert N) : Bool :=
  -- sizes are exactly N
  -- all entries are strictly < N
  -- inv[map[i]] = i for all i
  -- map[inv[i]] = i for all i
  ...

theorem FinMapArrayCert.bijective_of_ok
    {N : Nat}
    (C : FinMapArrayCert N)
    (h : C.ok = true) :
    Function.Bijective (C.mapFunOfOk h)
```

The `m=5` selector-layer tables have now been generated in
`D7Odd/Handoff/SmallLayer5SelectorData0.lean` through
`D7Odd/Handoff/SmallLayer5SelectorData6.lean`, and
`D7Odd/Handoff/SmallRank5Certificates.lean` proves `SmallCertificateTarget5`.
The same helper can be reused if a future small-case selector map needs a
finite inverse certificate.

## 6. Small-branch packaging

`RootFlatSchedule` and `RootFlatCertificate` now operate on the root-flat state
type `RootState7 m`, matching the handoff theorem and avoiding the impossible
stronger requirement that root-flat returns be single cycles on all of
`Vec7 m`.

`D7Odd/Handoff/SmallBranches.lean` packages the finite `m=3,5` certificates:

```lean
def smallRootFlatCertificate3 : RootFlatCertificate 3
def smallRootFlatCertificate5 : RootFlatCertificate 5

theorem smallHamilton3 : HamiltonDecompositionD7 3
theorem smallHamilton5 : HamiltonDecompositionD7 5

def smallBranchResults : SmallBranchResults
```

Thus the small odd branch is no longer an abstract input to the final
dispatcher, and the canonical generic branch realization is now supplied by
`canonical_realization_theorem`.
