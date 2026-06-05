import Shared.RankCycle

namespace EvenV11

namespace FiniteArrayCert

theorem bijective_of_inverse
    {α β : Type*} (f : α → β) (g : β → α)
    (hleft : ∀ x : α, g (f x) = x)
    (hright : ∀ y : β, f (g y) = y) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    calc
      x = g (f x) := (hleft x).symm
      _ = g (f y) := by rw [hxy]
      _ = y := hleft y
  · intro y
    exact ⟨g y, hright y⟩

theorem singleCycle_of_rankFun
    {N : Nat} [NeZero N]
    (next rank : Fin N → Fin N)
    (hRank : Function.Bijective rank)
    (hStep : ∀ i, rank (next i) = rank i + 1) :
    Shared.IsSingleCycleMap next := by
  refine Shared.single_cycle_of_zmod_rank
    (f := next)
    (rank := fun i => (ZMod.finEquiv N) (rank i))
    ?_ ?_
  · exact Function.Bijective.comp
      (Equiv.bijective (ZMod.finEquiv N).toEquiv) hRank
  · intro i
    have h := congrArg (fun r => (ZMod.finEquiv N) r) (hStep i)
    simpa using h

theorem single_cycle_of_bijective_semiconj
    {α β : Type*} (f : α → α) (g : β → β) (φ : α → β)
    (hφ : Function.Bijective φ)
    (hcomm : ∀ x : α, φ (f x) = g (φ x))
    (hf : Shared.IsSingleCycleMap f) :
    Shared.IsSingleCycleMap g := by
  have hcomm_iter :
      ∀ (n : Nat) (x : α), φ (f^[n] x) = g^[n] (φ x) := by
    intro n x
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hcomm, ih]
  have hg_inj : Function.Injective g := by
    intro y₁ y₂ hy
    rcases hφ.2 y₁ with ⟨x₁, rfl⟩
    rcases hφ.2 y₂ with ⟨x₂, rfl⟩
    rw [← hcomm x₁, ← hcomm x₂] at hy
    exact congrArg φ (hf.1.1 (hφ.1 hy))
  have hg_surj : Function.Surjective g := by
    intro y
    rcases hφ.2 y with ⟨x, rfl⟩
    rcases hf.1.2 x with ⟨x₀, hx₀⟩
    refine ⟨φ x₀, ?_⟩
    rw [← hcomm, hx₀]
  refine ⟨⟨hg_inj, hg_surj⟩, ?_⟩
  intro y₁ y₂
  rcases hφ.2 y₁ with ⟨x₁, rfl⟩
  rcases hφ.2 y₂ with ⟨x₂, rfl⟩
  rcases hf.2 x₁ x₂ with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← hcomm_iter, hn]

structure RankArrayCert (N : Nat) where
  next : Array Nat
  rank : Array Nat
  invRank : Array Nat

namespace RankArrayCert

def allUpTo (N : Nat) (p : Nat → Bool) : Bool :=
  (List.range N).all p

theorem allUpTo_true {N : Nat} {p : Nat → Bool}
    (h : allUpTo N p = true) {i : Nat} (hi : i < N) : p i = true := by
  exact (List.all_eq_true.mp h) i (List.mem_range.mpr hi)

def valuesLt (N : Nat) (a : Array Nat) : Bool :=
  allUpTo N fun i => decide (a.getD i 0 < N)

theorem valuesLt_true {N : Nat} {a : Array Nat}
    (h : valuesLt N a = true) :
    ∀ i : Fin N, a.getD i.val 0 < N := by
  intro i
  exact of_decide_eq_true (allUpTo_true h i.isLt)

def leftInvOk {N : Nat} (C : RankArrayCert N) : Bool :=
  allUpTo N fun i => decide (C.invRank.getD (C.rank.getD i 0) 0 = i)

def rightInvOk {N : Nat} (C : RankArrayCert N) : Bool :=
  allUpTo N fun r => decide (C.rank.getD (C.invRank.getD r 0) 0 = r)

def stepOk {N : Nat} (C : RankArrayCert N) : Bool :=
  allUpTo N fun i =>
    decide (C.rank.getD (C.next.getD i 0) 0 = (C.rank.getD i 0 + 1) % N)

theorem leftInvOk_true {N : Nat} {C : RankArrayCert N}
    (h : C.leftInvOk = true) :
    ∀ i : Fin N, C.invRank.getD (C.rank.getD i.val 0) 0 = i.val := by
  intro i
  exact of_decide_eq_true (allUpTo_true h i.isLt)

theorem rightInvOk_true {N : Nat} {C : RankArrayCert N}
    (h : C.rightInvOk = true) :
    ∀ r : Fin N, C.rank.getD (C.invRank.getD r.val 0) 0 = r.val := by
  intro r
  exact of_decide_eq_true (allUpTo_true h r.isLt)

theorem stepOk_true {N : Nat} {C : RankArrayCert N}
    (h : C.stepOk = true) :
    ∀ i : Fin N,
      C.rank.getD (C.next.getD i.val 0) 0 =
        (C.rank.getD i.val 0 + 1) % N := by
  intro i
  exact of_decide_eq_true (allUpTo_true h i.isLt)

def okParts {N : Nat} (C : RankArrayCert N) : List Bool :=
  [ decide (C.next.size = N)
  , decide (C.rank.size = N)
  , decide (C.invRank.size = N)
  , valuesLt N C.next
  , valuesLt N C.rank
  , valuesLt N C.invRank
  , leftInvOk C
  , rightInvOk C
  , stepOk C
  ]

def ok {N : Nat} (C : RankArrayCert N) : Bool :=
  C.okParts.all id

structure Valid {N : Nat} (C : RankArrayCert N) : Prop where
  next_size : C.next.size = N
  rank_size : C.rank.size = N
  invRank_size : C.invRank.size = N
  next_lt : ∀ i : Fin N, C.next.getD i.val 0 < N
  rank_lt : ∀ i : Fin N, C.rank.getD i.val 0 < N
  invRank_lt : ∀ r : Fin N, C.invRank.getD r.val 0 < N
  leftInv_val :
    ∀ i : Fin N, C.invRank.getD (C.rank.getD i.val 0) 0 = i.val
  rightInv_val :
    ∀ r : Fin N, C.rank.getD (C.invRank.getD r.val 0) 0 = r.val
  step_val : ∀ i : Fin N,
    C.rank.getD (C.next.getD i.val 0) 0 =
      (C.rank.getD i.val 0 + 1) % N

def nextFun {N : Nat} (C : RankArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.next.getD i.val 0, h.next_lt i⟩

def rankFun {N : Nat} (C : RankArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.rank.getD i.val 0, h.rank_lt i⟩

def invRankFun {N : Nat} (C : RankArrayCert N) (h : C.Valid) :
    Fin N → Fin N :=
  fun r => ⟨C.invRank.getD r.val 0, h.invRank_lt r⟩

theorem rankFun_left_inv {N : Nat} (C : RankArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.invRankFun h (C.rankFun h i) = i := by
  intro i
  apply Fin.ext
  change C.invRank.getD (C.rank.getD i.val 0) 0 = i.val
  exact h.leftInv_val i

theorem rankFun_inv {N : Nat} (C : RankArrayCert N) (h : C.Valid) :
    ∀ r : Fin N, C.rankFun h (C.invRankFun h r) = r := by
  intro r
  apply Fin.ext
  change C.rank.getD (C.invRank.getD r.val 0) 0 = r.val
  exact h.rightInv_val r

theorem rankFun_step {N : Nat} [NeZero N] (C : RankArrayCert N)
    (h : C.Valid) :
    ∀ i : Fin N, C.rankFun h (C.nextFun h i) = C.rankFun h i + 1 := by
  intro i
  apply Fin.ext
  dsimp [nextFun, rankFun]
  rw [Fin.val_add]
  simpa using h.step_val i

theorem rankFun_bijective {N : Nat} (C : RankArrayCert N) (h : C.Valid) :
    Function.Bijective (C.rankFun h) :=
  bijective_of_inverse (C.rankFun h) (C.invRankFun h)
    (rankFun_left_inv C h) (rankFun_inv C h)

noncomputable def rankEquiv {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.Valid) :
    Fin N ≃ ZMod N :=
  (Equiv.ofBijective (C.rankFun h) (C.rankFun_bijective h)).trans
    (ZMod.finEquiv N).toEquiv

theorem rankEquiv_step {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.rankEquiv h (C.nextFun h i) =
      C.rankEquiv h i + 1 := by
  intro i
  have hstep := congrArg (fun r => (ZMod.finEquiv N) r)
    (C.rankFun_step h i)
  simpa [rankEquiv] using hstep

theorem singleCycle_of_valid {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.Valid) :
    Shared.IsSingleCycleMap (C.nextFun h) := by
  exact singleCycle_of_rankFun
    (next := C.nextFun h)
    (rank := C.rankFun h)
    (C.rankFun_bijective h)
    (C.rankFun_step h)

theorem valid_of_ok {N : Nat} (C : RankArrayCert N) (h : C.ok = true) :
    C.Valid := by
  have hparts : ∀ b ∈ C.okParts, id b = true := by
    exact List.all_eq_true.mp (by simpa [ok] using h)
  have hNextSizeBool : decide (C.next.size = N) = true := by
    simpa using hparts (decide (C.next.size = N)) (by simp [okParts])
  have hRankSizeBool : decide (C.rank.size = N) = true := by
    simpa using hparts (decide (C.rank.size = N)) (by simp [okParts])
  have hInvRankSizeBool : decide (C.invRank.size = N) = true := by
    simpa using hparts (decide (C.invRank.size = N)) (by simp [okParts])
  have hNextLtBool : valuesLt N C.next = true := by
    simpa using hparts (valuesLt N C.next) (by simp [okParts])
  have hRankLtBool : valuesLt N C.rank = true := by
    simpa using hparts (valuesLt N C.rank) (by simp [okParts])
  have hInvRankLtBool : valuesLt N C.invRank = true := by
    simpa using hparts (valuesLt N C.invRank) (by simp [okParts])
  have hLeftInvBool : C.leftInvOk = true := by
    simpa using hparts C.leftInvOk (by simp [okParts])
  have hRightInvBool : C.rightInvOk = true := by
    simpa using hparts C.rightInvOk (by simp [okParts])
  have hStepBool : C.stepOk = true := by
    simpa using hparts C.stepOk (by simp [okParts])
  exact
    { next_size := of_decide_eq_true hNextSizeBool
      rank_size := of_decide_eq_true hRankSizeBool
      invRank_size := of_decide_eq_true hInvRankSizeBool
      next_lt := valuesLt_true hNextLtBool
      rank_lt := valuesLt_true hRankLtBool
      invRank_lt := valuesLt_true hInvRankLtBool
      leftInv_val := leftInvOk_true hLeftInvBool
      rightInv_val := rightInvOk_true hRightInvBool
      step_val := stepOk_true hStepBool }

def nextFunOfOk {N : Nat} (C : RankArrayCert N) (h : C.ok = true) :
    Fin N → Fin N :=
  C.nextFun (valid_of_ok C h)

noncomputable def rankEquivOfOk {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.ok = true) :
    Fin N ≃ ZMod N :=
  C.rankEquiv (valid_of_ok C h)

theorem rankEquivOfOk_step {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.ok = true) :
    ∀ i : Fin N, C.rankEquivOfOk h (C.nextFunOfOk h i) =
      C.rankEquivOfOk h i + 1 :=
  C.rankEquiv_step (valid_of_ok C h)

theorem singleCycle_of_ok {N : Nat} [NeZero N]
    (C : RankArrayCert N) (h : C.ok = true) :
    Shared.IsSingleCycleMap (C.nextFunOfOk h) :=
  singleCycle_of_valid C (valid_of_ok C h)

end RankArrayCert

structure FinMapArrayCert (N : Nat) where
  map : Array Nat
  inv : Array Nat

namespace FinMapArrayCert

structure Valid {N : Nat} (C : FinMapArrayCert N) : Prop where
  map_size : C.map.size = N
  inv_size : C.inv.size = N
  map_lt : ∀ i : Fin N, C.map.getD i.val 0 < N
  inv_lt : ∀ i : Fin N, C.inv.getD i.val 0 < N
  leftInv_val : ∀ i : Fin N, C.inv.getD (C.map.getD i.val 0) 0 = i.val
  rightInv_val : ∀ i : Fin N, C.map.getD (C.inv.getD i.val 0) 0 = i.val

def mapFun {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.map.getD i.val 0, h.map_lt i⟩

def invFun {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) : Fin N → Fin N :=
  fun i => ⟨C.inv.getD i.val 0, h.inv_lt i⟩

theorem mapFun_left_inv {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.invFun h (C.mapFun h i) = i := by
  intro i
  apply Fin.ext
  change C.inv.getD (C.map.getD i.val 0) 0 = i.val
  exact h.leftInv_val i

theorem mapFun_inv {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) :
    ∀ i : Fin N, C.mapFun h (C.invFun h i) = i := by
  intro i
  apply Fin.ext
  change C.map.getD (C.inv.getD i.val 0) 0 = i.val
  exact h.rightInv_val i

theorem bijective_of_valid {N : Nat} (C : FinMapArrayCert N) (h : C.Valid) :
  Function.Bijective (C.mapFun h) :=
  bijective_of_inverse (C.mapFun h) (C.invFun h)
    (mapFun_left_inv C h) (mapFun_inv C h)

def leftInvOk {N : Nat} (C : FinMapArrayCert N) : Bool :=
  RankArrayCert.allUpTo N fun i =>
    decide (C.inv.getD (C.map.getD i 0) 0 = i)

def rightInvOk {N : Nat} (C : FinMapArrayCert N) : Bool :=
  RankArrayCert.allUpTo N fun i =>
    decide (C.map.getD (C.inv.getD i 0) 0 = i)

theorem leftInvOk_true {N : Nat} {C : FinMapArrayCert N}
    (h : C.leftInvOk = true) :
    ∀ i : Fin N, C.inv.getD (C.map.getD i.val 0) 0 = i.val := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

theorem rightInvOk_true {N : Nat} {C : FinMapArrayCert N}
    (h : C.rightInvOk = true) :
    ∀ i : Fin N, C.map.getD (C.inv.getD i.val 0) 0 = i.val := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

def okParts {N : Nat} (C : FinMapArrayCert N) : List Bool :=
  [ decide (C.map.size = N)
  , decide (C.inv.size = N)
  , RankArrayCert.valuesLt N C.map
  , RankArrayCert.valuesLt N C.inv
  , leftInvOk C
  , rightInvOk C
  ]

def ok {N : Nat} (C : FinMapArrayCert N) : Bool :=
  C.okParts.all id

theorem valid_of_ok {N : Nat} (C : FinMapArrayCert N) (h : C.ok = true) :
    C.Valid := by
  have hparts : ∀ b ∈ C.okParts, id b = true := by
    exact List.all_eq_true.mp (by simpa [ok] using h)
  have hMapSizeBool : decide (C.map.size = N) = true := by
    simpa using hparts (decide (C.map.size = N)) (by simp [okParts])
  have hInvSizeBool : decide (C.inv.size = N) = true := by
    simpa using hparts (decide (C.inv.size = N)) (by simp [okParts])
  have hMapLtBool : RankArrayCert.valuesLt N C.map = true := by
    simpa using hparts (RankArrayCert.valuesLt N C.map) (by simp [okParts])
  have hInvLtBool : RankArrayCert.valuesLt N C.inv = true := by
    simpa using hparts (RankArrayCert.valuesLt N C.inv) (by simp [okParts])
  have hLeftInvBool : C.leftInvOk = true := by
    simpa using hparts C.leftInvOk (by simp [okParts])
  have hRightInvBool : C.rightInvOk = true := by
    simpa using hparts C.rightInvOk (by simp [okParts])
  exact
    { map_size := of_decide_eq_true hMapSizeBool
      inv_size := of_decide_eq_true hInvSizeBool
      map_lt := RankArrayCert.valuesLt_true hMapLtBool
      inv_lt := RankArrayCert.valuesLt_true hInvLtBool
      leftInv_val := leftInvOk_true hLeftInvBool
      rightInv_val := rightInvOk_true hRightInvBool }

def mapFunOfOk {N : Nat} (C : FinMapArrayCert N) (h : C.ok = true) :
    Fin N → Fin N :=
  C.mapFun (valid_of_ok C h)

theorem bijective_of_ok {N : Nat} (C : FinMapArrayCert N)
    (h : C.ok = true) :
    Function.Bijective (C.mapFunOfOk h) :=
  bijective_of_valid C (valid_of_ok C h)

end FinMapArrayCert

namespace Blob

def b64Val (ch : Char) : Nat :=
  let n := ch.toNat
  if n = 95 then 62
  else if n = 45 then 63
  else if n < 48 then 0
  else if n <= 57 then n - 48
  else if n < 65 then 0
  else if n <= 90 then 10 + (n - 65)
  else if n < 97 then 0
  else if n <= 122 then 36 + (n - 97)
  else 0

def charAtVal (blob : String) (pos : Nat) : Nat :=
  match String.Pos.Raw.get? blob ⟨pos⟩ with
  | some ch => b64Val ch
  | none => 0

def fixedBase64GetAux (blob : String) : Nat → Nat → Nat → Nat
  | _pos, 0, acc => acc
  | pos, width + 1, acc =>
      fixedBase64GetAux blob (pos + 1) width
        (acc * 64 + charAtVal blob pos)

def fixedBase64Get (width : Nat) (blob : String) (i : Nat) : Nat :=
  fixedBase64GetAux blob (i * width) width 0

structure RankBlobCert (N width : Nat) where
  next : String
  rank : String
  invRank : String

namespace RankBlobCert

def nextVal {N width : Nat} (C : RankBlobCert N width) (i : Nat) : Nat :=
  fixedBase64Get width C.next i

def rankVal {N width : Nat} (C : RankBlobCert N width) (i : Nat) : Nat :=
  fixedBase64Get width C.rank i

def invRankVal {N width : Nat} (C : RankBlobCert N width) (i : Nat) : Nat :=
  fixedBase64Get width C.invRank i

def valuesLt (N : Nat) (width : Nat) (blob : String) : Bool :=
  RankArrayCert.allUpTo N fun i => decide (fixedBase64Get width blob i < N)

theorem valuesLt_true {N width : Nat} {blob : String}
    (h : valuesLt N width blob = true) :
    ∀ i : Fin N, fixedBase64Get width blob i < N := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

def leftInvOk {N width : Nat} (C : RankBlobCert N width) : Bool :=
  RankArrayCert.allUpTo N fun i =>
    decide (C.invRankVal (C.rankVal i) = i)

def rightInvOk {N width : Nat} (C : RankBlobCert N width) : Bool :=
  RankArrayCert.allUpTo N fun r =>
    decide (C.rankVal (C.invRankVal r) = r)

def stepOk {N width : Nat} (C : RankBlobCert N width) : Bool :=
  RankArrayCert.allUpTo N fun i =>
    decide (C.rankVal (C.nextVal i) = (C.rankVal i + 1) % N)

theorem leftInvOk_true {N width : Nat} {C : RankBlobCert N width}
    (h : C.leftInvOk = true) :
    ∀ i : Fin N, C.invRankVal (C.rankVal i.val) = i.val := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

theorem rightInvOk_true {N width : Nat} {C : RankBlobCert N width}
    (h : C.rightInvOk = true) :
    ∀ r : Fin N, C.rankVal (C.invRankVal r.val) = r.val := by
  intro r
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h r.isLt)

theorem stepOk_true {N width : Nat} {C : RankBlobCert N width}
    (h : C.stepOk = true) :
    ∀ i : Fin N, C.rankVal (C.nextVal i.val) =
      (C.rankVal i.val + 1) % N := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

def okParts {N width : Nat} (C : RankBlobCert N width) : List Bool :=
  [ decide (C.next.length = N * width)
  , decide (C.rank.length = N * width)
  , decide (C.invRank.length = N * width)
  , valuesLt N width C.next
  , valuesLt N width C.rank
  , valuesLt N width C.invRank
  , leftInvOk C
  , rightInvOk C
  , stepOk C
  ]

def ok {N width : Nat} (C : RankBlobCert N width) : Bool :=
  C.okParts.all id

structure Valid {N width : Nat} (C : RankBlobCert N width) : Prop where
  next_size : C.next.length = N * width
  rank_size : C.rank.length = N * width
  invRank_size : C.invRank.length = N * width
  next_lt : ∀ i : Fin N, C.nextVal i.val < N
  rank_lt : ∀ i : Fin N, C.rankVal i.val < N
  invRank_lt : ∀ r : Fin N, C.invRankVal r.val < N
  leftInv_val : ∀ i : Fin N, C.invRankVal (C.rankVal i.val) = i.val
  rightInv_val : ∀ r : Fin N, C.rankVal (C.invRankVal r.val) = r.val
  step_val : ∀ i : Fin N,
    C.rankVal (C.nextVal i.val) = (C.rankVal i.val + 1) % N

def nextFun {N width : Nat} (C : RankBlobCert N width) (h : C.Valid) :
    Fin N → Fin N :=
  fun i => ⟨C.nextVal i.val, h.next_lt i⟩

def rankFun {N width : Nat} (C : RankBlobCert N width) (h : C.Valid) :
    Fin N → Fin N :=
  fun i => ⟨C.rankVal i.val, h.rank_lt i⟩

def invRankFun {N width : Nat} (C : RankBlobCert N width) (h : C.Valid) :
    Fin N → Fin N :=
  fun r => ⟨C.invRankVal r.val, h.invRank_lt r⟩

theorem rankFun_left_inv {N width : Nat} (C : RankBlobCert N width)
    (h : C.Valid) :
    ∀ i : Fin N, C.invRankFun h (C.rankFun h i) = i := by
  intro i
  apply Fin.ext
  change C.invRankVal (C.rankVal i.val) = i.val
  exact h.leftInv_val i

theorem rankFun_inv {N width : Nat} (C : RankBlobCert N width)
    (h : C.Valid) :
    ∀ r : Fin N, C.rankFun h (C.invRankFun h r) = r := by
  intro r
  apply Fin.ext
  change C.rankVal (C.invRankVal r.val) = r.val
  exact h.rightInv_val r

theorem rankFun_step {N width : Nat} [NeZero N]
    (C : RankBlobCert N width) (h : C.Valid) :
    ∀ i : Fin N, C.rankFun h (C.nextFun h i) = C.rankFun h i + 1 := by
  intro i
  apply Fin.ext
  dsimp [nextFun, rankFun]
  rw [Fin.val_add]
  simpa using h.step_val i

theorem rankFun_bijective {N width : Nat} (C : RankBlobCert N width)
    (h : C.Valid) :
    Function.Bijective (C.rankFun h) :=
  bijective_of_inverse (C.rankFun h) (C.invRankFun h)
    (rankFun_left_inv C h) (rankFun_inv C h)

noncomputable def rankEquiv {N width : Nat} [NeZero N]
    (C : RankBlobCert N width) (h : C.Valid) :
    Fin N ≃ ZMod N :=
  (Equiv.ofBijective (C.rankFun h) (C.rankFun_bijective h)).trans
    (ZMod.finEquiv N).toEquiv

theorem rankEquiv_step {N width : Nat} [NeZero N]
    (C : RankBlobCert N width) (h : C.Valid) :
    ∀ i : Fin N, C.rankEquiv h (C.nextFun h i) =
      C.rankEquiv h i + 1 := by
  intro i
  have hstep := congrArg (fun r => (ZMod.finEquiv N) r)
    (C.rankFun_step h i)
  simpa [rankEquiv] using hstep

theorem singleCycle_of_valid {N width : Nat} [NeZero N]
    (C : RankBlobCert N width) (h : C.Valid) :
    Shared.IsSingleCycleMap (C.nextFun h) := by
  exact singleCycle_of_rankFun
    (next := C.nextFun h)
    (rank := C.rankFun h)
    (C.rankFun_bijective h)
    (C.rankFun_step h)

theorem valid_of_ok {N width : Nat} (C : RankBlobCert N width)
    (h : C.ok = true) : C.Valid := by
  have hparts : ∀ b ∈ C.okParts, id b = true := by
    exact List.all_eq_true.mp (by simpa [ok] using h)
  have hNextSizeBool : decide (C.next.length = N * width) = true := by
    simpa using hparts (decide (C.next.length = N * width)) (by simp [okParts])
  have hRankSizeBool : decide (C.rank.length = N * width) = true := by
    simpa using hparts (decide (C.rank.length = N * width)) (by simp [okParts])
  have hInvRankSizeBool : decide (C.invRank.length = N * width) = true := by
    simpa using hparts (decide (C.invRank.length = N * width)) (by simp [okParts])
  have hNextLtBool : valuesLt N width C.next = true := by
    simpa using hparts (valuesLt N width C.next) (by simp [okParts])
  have hRankLtBool : valuesLt N width C.rank = true := by
    simpa using hparts (valuesLt N width C.rank) (by simp [okParts])
  have hInvRankLtBool : valuesLt N width C.invRank = true := by
    simpa using hparts (valuesLt N width C.invRank) (by simp [okParts])
  have hLeftInvBool : C.leftInvOk = true := by
    simpa using hparts C.leftInvOk (by simp [okParts])
  have hRightInvBool : C.rightInvOk = true := by
    simpa using hparts C.rightInvOk (by simp [okParts])
  have hStepBool : C.stepOk = true := by
    simpa using hparts C.stepOk (by simp [okParts])
  exact
    { next_size := of_decide_eq_true hNextSizeBool
      rank_size := of_decide_eq_true hRankSizeBool
      invRank_size := of_decide_eq_true hInvRankSizeBool
      next_lt := valuesLt_true hNextLtBool
      rank_lt := valuesLt_true hRankLtBool
      invRank_lt := valuesLt_true hInvRankLtBool
      leftInv_val := leftInvOk_true hLeftInvBool
      rightInv_val := rightInvOk_true hRightInvBool
      step_val := stepOk_true hStepBool }

def nextFunOfOk {N width : Nat} (C : RankBlobCert N width)
    (h : C.ok = true) : Fin N → Fin N :=
  C.nextFun (valid_of_ok C h)

noncomputable def rankEquivOfOk {N width : Nat} [NeZero N]
    (C : RankBlobCert N width) (h : C.ok = true) :
    Fin N ≃ ZMod N :=
  C.rankEquiv (valid_of_ok C h)

theorem rankEquivOfOk_step {N width : Nat} [NeZero N]
    (C : RankBlobCert N width) (h : C.ok = true) :
    ∀ i : Fin N, C.rankEquivOfOk h (C.nextFunOfOk h i) =
      C.rankEquivOfOk h i + 1 :=
  C.rankEquiv_step (valid_of_ok C h)

theorem singleCycle_of_ok {N width : Nat} [NeZero N]
    (C : RankBlobCert N width) (h : C.ok = true) :
    Shared.IsSingleCycleMap (C.nextFunOfOk h) :=
  singleCycle_of_valid C (valid_of_ok C h)

end RankBlobCert

structure FinMapBlobCert (N width : Nat) where
  map : String
  inv : String

namespace FinMapBlobCert

def mapVal {N width : Nat} (C : FinMapBlobCert N width) (i : Nat) : Nat :=
  fixedBase64Get width C.map i

def invVal {N width : Nat} (C : FinMapBlobCert N width) (i : Nat) : Nat :=
  fixedBase64Get width C.inv i

def leftInvOk {N width : Nat} (C : FinMapBlobCert N width) : Bool :=
  RankArrayCert.allUpTo N fun i => decide (C.invVal (C.mapVal i) = i)

def rightInvOk {N width : Nat} (C : FinMapBlobCert N width) : Bool :=
  RankArrayCert.allUpTo N fun i => decide (C.mapVal (C.invVal i) = i)

theorem leftInvOk_true {N width : Nat} {C : FinMapBlobCert N width}
    (h : C.leftInvOk = true) :
    ∀ i : Fin N, C.invVal (C.mapVal i.val) = i.val := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

theorem rightInvOk_true {N width : Nat} {C : FinMapBlobCert N width}
    (h : C.rightInvOk = true) :
    ∀ i : Fin N, C.mapVal (C.invVal i.val) = i.val := by
  intro i
  exact of_decide_eq_true (RankArrayCert.allUpTo_true h i.isLt)

def okParts {N width : Nat} (C : FinMapBlobCert N width) : List Bool :=
  [ decide (C.map.length = N * width)
  , decide (C.inv.length = N * width)
  , RankBlobCert.valuesLt N width C.map
  , RankBlobCert.valuesLt N width C.inv
  , leftInvOk C
  , rightInvOk C
  ]

def ok {N width : Nat} (C : FinMapBlobCert N width) : Bool :=
  C.okParts.all id

structure Valid {N width : Nat} (C : FinMapBlobCert N width) : Prop where
  map_size : C.map.length = N * width
  inv_size : C.inv.length = N * width
  map_lt : ∀ i : Fin N, C.mapVal i.val < N
  inv_lt : ∀ i : Fin N, C.invVal i.val < N
  leftInv_val : ∀ i : Fin N, C.invVal (C.mapVal i.val) = i.val
  rightInv_val : ∀ i : Fin N, C.mapVal (C.invVal i.val) = i.val

def mapFun {N width : Nat} (C : FinMapBlobCert N width) (h : C.Valid) :
    Fin N → Fin N :=
  fun i => ⟨C.mapVal i.val, h.map_lt i⟩

def invFun {N width : Nat} (C : FinMapBlobCert N width) (h : C.Valid) :
    Fin N → Fin N :=
  fun i => ⟨C.invVal i.val, h.inv_lt i⟩

theorem mapFun_left_inv {N width : Nat} (C : FinMapBlobCert N width)
    (h : C.Valid) :
    ∀ i : Fin N, C.invFun h (C.mapFun h i) = i := by
  intro i
  apply Fin.ext
  change C.invVal (C.mapVal i.val) = i.val
  exact h.leftInv_val i

theorem mapFun_inv {N width : Nat} (C : FinMapBlobCert N width)
    (h : C.Valid) :
    ∀ i : Fin N, C.mapFun h (C.invFun h i) = i := by
  intro i
  apply Fin.ext
  change C.mapVal (C.invVal i.val) = i.val
  exact h.rightInv_val i

theorem bijective_of_valid {N width : Nat} (C : FinMapBlobCert N width)
    (h : C.Valid) :
    Function.Bijective (C.mapFun h) :=
  bijective_of_inverse (C.mapFun h) (C.invFun h)
    (mapFun_left_inv C h) (mapFun_inv C h)

theorem valid_of_ok {N width : Nat} (C : FinMapBlobCert N width)
    (h : C.ok = true) : C.Valid := by
  have hparts : ∀ b ∈ C.okParts, id b = true := by
    exact List.all_eq_true.mp (by simpa [ok] using h)
  have hMapSizeBool : decide (C.map.length = N * width) = true := by
    simpa using hparts (decide (C.map.length = N * width)) (by simp [okParts])
  have hInvSizeBool : decide (C.inv.length = N * width) = true := by
    simpa using hparts (decide (C.inv.length = N * width)) (by simp [okParts])
  have hMapLtBool : RankBlobCert.valuesLt N width C.map = true := by
    simpa using hparts (RankBlobCert.valuesLt N width C.map) (by simp [okParts])
  have hInvLtBool : RankBlobCert.valuesLt N width C.inv = true := by
    simpa using hparts (RankBlobCert.valuesLt N width C.inv) (by simp [okParts])
  have hLeftInvBool : C.leftInvOk = true := by
    simpa using hparts C.leftInvOk (by simp [okParts])
  have hRightInvBool : C.rightInvOk = true := by
    simpa using hparts C.rightInvOk (by simp [okParts])
  exact
    { map_size := of_decide_eq_true hMapSizeBool
      inv_size := of_decide_eq_true hInvSizeBool
      map_lt := RankBlobCert.valuesLt_true hMapLtBool
      inv_lt := RankBlobCert.valuesLt_true hInvLtBool
      leftInv_val := leftInvOk_true hLeftInvBool
      rightInv_val := rightInvOk_true hRightInvBool }

def mapFunOfOk {N width : Nat} (C : FinMapBlobCert N width)
    (h : C.ok = true) : Fin N → Fin N :=
  C.mapFun (valid_of_ok C h)

theorem bijective_of_ok {N width : Nat} (C : FinMapBlobCert N width)
    (h : C.ok = true) :
    Function.Bijective (C.mapFunOfOk h) :=
  bijective_of_valid C (valid_of_ok C h)

end FinMapBlobCert

end Blob

end FiniteArrayCert
end EvenV11
