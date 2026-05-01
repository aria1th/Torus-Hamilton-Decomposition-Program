import Shared.TorusCayley
import Shared.Monodromy

namespace Shared

structure CoordinatizedCayleyDecomposition (d m : Nat) [NeZero (m ^ d)] extends
    CayleyDecomposition d m where
  cycleCoordinate :
    ∀ c : TorusColor d, CycleCoordinate (m ^ d) (cayleyColorStep colorDir c)

def CoordinatizedCayleyHamiltonDecomposition (d m : Nat) : Prop :=
  ∃ h : NeZero (m ^ d), Nonempty (@CoordinatizedCayleyDecomposition d m h)

theorem cayleyHamiltonDecomposition_of_coordinatized
    {d m : Nat} :
    CoordinatizedCayleyHamiltonDecomposition d m →
      CayleyHamiltonDecomposition d m := by
  rintro ⟨_h, ⟨D⟩⟩
  exact ⟨D.toCayleyDecomposition⟩

noncomputable def coordinatizedCayleyDecomposition_of_rank
    {d m : Nat} [NeZero (m ^ d)]
    (D : CayleyDecomposition d m)
    (rank : TorusColor d → TorusVertex d m → ZMod (m ^ d))
    (hrank : ∀ c : TorusColor d, Function.Bijective (rank c))
    (hstep : ∀ c : TorusColor d, ∀ x : TorusVertex d m,
      rank c (cayleyColorStep D.colorDir c x) = rank c x + 1) :
    CoordinatizedCayleyDecomposition d m where
  toCayleyDecomposition := D
  cycleCoordinate := fun c =>
    CycleCoordinate.ofRank (rank c) (hrank c) (hstep c)

theorem coordinatizedCayleyHamiltonDecomposition_of_rank
    {d m : Nat} [NeZero (m ^ d)]
    (D : CayleyDecomposition d m)
    (rank : TorusColor d → TorusVertex d m → ZMod (m ^ d))
    (hrank : ∀ c : TorusColor d, Function.Bijective (rank c))
    (hstep : ∀ c : TorusColor d, ∀ x : TorusVertex d m,
      rank c (cayleyColorStep D.colorDir c x) = rank c x + 1) :
    CoordinatizedCayleyHamiltonDecomposition d m := by
  exact ⟨inferInstance,
    ⟨coordinatizedCayleyDecomposition_of_rank D rank hrank hstep⟩⟩

noncomputable def coordinatizedCayleyDecomposition_of_single_cycle
    {d m : Nat} [NeZero m] [NeZero (m ^ d)]
    (hm : 1 < m ^ d)
    (D : CayleyDecomposition d m) :
    CoordinatizedCayleyDecomposition d m where
  toCayleyDecomposition := D
  cycleCoordinate := fun c =>
    CycleCoordinate.ofFiniteSingleCycle
      (f := cayleyColorStep D.colorDir c)
      (by simp [TorusVertex])
      hm
      (D.colorHamiltonian c)

theorem coordinatizedCayleyHamiltonDecomposition_of_single_cycle
    {d m : Nat} [NeZero m] [NeZero (m ^ d)]
    (hm : 1 < m ^ d)
    (h : CayleyHamiltonDecomposition d m) :
    CoordinatizedCayleyHamiltonDecomposition d m := by
  rcases h with ⟨D⟩
  exact ⟨inferInstance,
    ⟨coordinatizedCayleyDecomposition_of_single_cycle hm D⟩⟩

def torusVertexBlockRankEquiv
    {a b m n : Nat} [NeZero n]
    {f : TorusVertex a m → TorusVertex a m}
    (C : CycleCoordinate n f) :
    TorusVertex (a * b) m ≃ TorusVertex b n where
  toFun x := fun j => C.equiv.symm ((torusVertexBlockEquiv a b m x) j)
  invFun y := (torusVertexBlockEquiv a b m).symm (fun j => C.equiv (y j))
  left_inv := by
    intro x
    have hblocks :
        (fun j => C.equiv (C.equiv.symm ((torusVertexBlockEquiv a b m x) j))) =
          torusVertexBlockEquiv a b m x := by
      funext j
      simp
    change (torusVertexBlockEquiv a b m).symm
        (fun j => C.equiv
          (C.equiv.symm ((torusVertexBlockEquiv a b m x) j))) = x
    rw [hblocks]
    simp
  right_inv := by
    intro y
    funext j
    calc
      C.equiv.symm
          ((torusVertexBlockEquiv a b m)
            ((torusVertexBlockEquiv a b m).symm
              (fun j => C.equiv (y j))) j) =
          C.equiv.symm (C.equiv (y j)) := by
            simp
      _ = y j := by simp

theorem torusVertexBlockRankEquiv_apply
    {a b m n : Nat} [NeZero n]
    {f : TorusVertex a m → TorusVertex a m}
    (C : CycleCoordinate n f)
    (x : TorusVertex (a * b) m) (j : Fin b) :
    torusVertexBlockRankEquiv (a := a) (b := b) (m := m) C x j =
      C.equiv.symm ((torusVertexBlockEquiv a b m x) j) := by
  rfl

theorem torusVertexBlockRankEquiv_symm_apply
    {a b m n : Nat} [NeZero n]
    {f : TorusVertex a m → TorusVertex a m}
    (C : CycleCoordinate n f)
    (y : TorusVertex b n) (j : Fin b) :
    torusVertexBlockEquiv a b m
        ((torusVertexBlockRankEquiv (a := a) (b := b) (m := m) C).symm y) j =
      C.equiv (y j) := by
  exact congrFun ((torusVertexBlockEquiv a b m).right_inv
    (fun j => C.equiv (y j))) j

def productCayleyColorDir
    {a b m : Nat} [NeZero (m ^ a)]
    (A : CayleyDecomposition a m)
    (B : CayleyDecomposition b (m ^ a))
    (coordA :
      ∀ c : TorusColor a, CycleCoordinate (m ^ a) (cayleyColorStep A.colorDir c)) :
    TorusColor (a * b) → TorusVertex (a * b) m → TorusDirection (a * b) :=
  fun c x =>
    let cb : TorusColor b := ((blockIndexEquiv a b).symm c).1
    let ca : TorusColor a := ((blockIndexEquiv a b).symm c).2
    let blocks : Fin b → TorusVertex a m := torusVertexBlockEquiv a b m x
    let ranks : TorusVertex b (m ^ a) :=
      fun j => (coordA ca).equiv.symm (blocks j)
    let j : TorusDirection b := B.colorDir cb ranks
    blockIndexEquiv a b (j, A.colorDir ca (blocks j))

theorem productCayleyColorDir_pair
    {a b m : Nat} [NeZero (m ^ a)]
    (A : CayleyDecomposition a m)
    (B : CayleyDecomposition b (m ^ a))
    (coordA :
      ∀ c : TorusColor a, CycleCoordinate (m ^ a) (cayleyColorStep A.colorDir c))
    (cb : TorusColor b) (ca : TorusColor a)
    (x : TorusVertex (a * b) m) :
    productCayleyColorDir A B coordA (blockIndexEquiv a b (cb, ca)) x =
      let blocks : Fin b → TorusVertex a m := torusVertexBlockEquiv a b m x
      let ranks : TorusVertex b (m ^ a) :=
        fun j => (coordA ca).equiv.symm (blocks j)
      let j : TorusDirection b := B.colorDir cb ranks
      blockIndexEquiv a b (j, A.colorDir ca (blocks j)) := by
  have hidx :
      (blockIndexEquiv a b).symm (blockIndexEquiv a b (cb, ca)) = (cb, ca) := by
    simp
  dsimp [productCayleyColorDir]
  rw [hidx]

theorem productCayleyColorDir_edgePartition
    {a b m : Nat} [NeZero (m ^ a)]
    (A : CayleyDecomposition a m)
    (B : CayleyDecomposition b (m ^ a))
    (coordA :
      ∀ c : TorusColor a, CycleCoordinate (m ^ a) (cayleyColorStep A.colorDir c)) :
    IsCayleyEdgePartition (productCayleyColorDir A B coordA) := by
  intro x k
  let ji : Fin b × Fin a := (blockIndexEquiv a b).symm k
  let j : Fin b := ji.1
  let i : Fin a := ji.2
  let blocks : Fin b → TorusVertex a m := torusVertexBlockEquiv a b m x
  rcases A.edgePartition (blocks j) i with ⟨ca, hca, hca_unique⟩
  let ranks : TorusVertex b (m ^ a) :=
    fun q => (coordA ca).equiv.symm (blocks q)
  rcases B.edgePartition ranks j with ⟨cb, hcb, hcb_unique⟩
  refine ⟨blockIndexEquiv a b (cb, ca), ?_, ?_⟩
  · have hk : blockIndexEquiv a b (j, i) = k := by
      simp [ji, j, i]
    have hidx :
        (blockIndexEquiv a b).symm (blockIndexEquiv a b (cb, ca)) = (cb, ca) := by
      simp
    rw [← hk]
    change productCayleyColorDir A B coordA (blockIndexEquiv a b (cb, ca)) x =
      blockIndexEquiv a b (j, i)
    rw [productCayleyColorDir_pair]
    change (blockIndexEquiv a b)
        (B.colorDir cb ranks, A.colorDir ca (blocks (B.colorDir cb ranks))) =
      blockIndexEquiv a b (j, i)
    have hpair :
        (B.colorDir cb ranks, A.colorDir ca (blocks (B.colorDir cb ranks))) =
          (j, i) := by
      apply Prod.ext
      · simpa [ranks, blocks] using hcb
      · simpa [ranks, blocks, hcb] using hca
    exact congrArg (blockIndexEquiv a b) hpair
  · intro c hc
    let cba : Fin b × Fin a := (blockIndexEquiv a b).symm c
    let cb' : Fin b := cba.1
    let ca' : Fin a := cba.2
    have hc_pair :
        (B.colorDir cb'
            (fun q => (coordA ca').equiv.symm (blocks q)),
          A.colorDir ca'
            (blocks
              (B.colorDir cb'
                (fun q => (coordA ca').equiv.symm (blocks q))))) = (j, i) := by
      have hk : blockIndexEquiv a b (j, i) = k := by
        simp [ji, j, i]
      apply (blockIndexEquiv a b).injective
      rw [hk]
      simpa [productCayleyColorDir, cba, cb', ca', blocks] using hc
    have hcb' :
        B.colorDir cb'
            (fun q => (coordA ca').equiv.symm (blocks q)) = j :=
      congrArg Prod.fst hc_pair
    have hca' : A.colorDir ca' (blocks j) = i := by
      have hsnd := congrArg Prod.snd hc_pair
      simpa [hcb'] using hsnd
    have hca_eq : ca' = ca := hca_unique ca' hca'
    have hcb_eq : cb' = cb := by
      rw [hca_eq] at hcb'
      exact hcb_unique cb' (by simpa [ranks] using hcb')
    have hcba_eq : cba = (cb, ca) := by
      ext <;> simp [cba, cb', ca', hcb_eq, hca_eq]
    apply (blockIndexEquiv a b).symm.injective
    calc
      (blockIndexEquiv a b).symm c = cba := rfl
      _ = (cb, ca) := hcba_eq
      _ = (blockIndexEquiv a b).symm (blockIndexEquiv a b (cb, ca)) := by simp

theorem productCayleyColorStep_rank
    {a b m : Nat} [NeZero (m ^ a)]
    (A : CayleyDecomposition a m)
    (B : CayleyDecomposition b (m ^ a))
    (coordA :
      ∀ c : TorusColor a, CycleCoordinate (m ^ a) (cayleyColorStep A.colorDir c))
    (cb : TorusColor b) (ca : TorusColor a)
    (x : TorusVertex (a * b) m) :
    torusVertexBlockRankEquiv (a := a) (b := b) (m := m) (coordA ca)
        (cayleyColorStep (productCayleyColorDir A B coordA)
          (blockIndexEquiv a b (cb, ca)) x) =
      cayleyColorStep B.colorDir cb
        (torusVertexBlockRankEquiv (a := a) (b := b) (m := m) (coordA ca) x) := by
  let C := coordA ca
  let blocks : Fin b → TorusVertex a m := torusVertexBlockEquiv a b m x
  let ranks : TorusVertex b (m ^ a) :=
    torusVertexBlockRankEquiv (a := a) (b := b) (m := m) C x
  let j : Fin b := B.colorDir cb ranks
  have hdir :
      productCayleyColorDir A B coordA (blockIndexEquiv a b (cb, ca)) x =
        blockIndexEquiv a b (j, A.colorDir ca (blocks j)) := by
    rw [productCayleyColorDir_pair]
    rfl
  funext q
  by_cases hq : q = j
  · subst q
    have hblock :
        torusVertexBlockEquiv a b m
            (x + torusBasis (a * b) m
              (blockIndexEquiv a b (j, A.colorDir ca (blocks j)))) j =
          cayleyColorStep A.colorDir ca (blocks j) := by
      simp [cayleyColorStep, blocks, torusVertexBlockEquiv_add_torusBasis_apply]
    calc
      torusVertexBlockRankEquiv (a := a) (b := b) (m := m) (coordA ca)
          (cayleyColorStep (productCayleyColorDir A B coordA)
            (blockIndexEquiv a b (cb, ca)) x) j =
          C.equiv.symm
            (torusVertexBlockEquiv a b m
              (x + torusBasis (a * b) m
                (blockIndexEquiv a b (j, A.colorDir ca (blocks j)))) j) := by
            simp [torusVertexBlockRankEquiv_apply, cayleyColorStep, C, hdir]
      _ = C.equiv.symm (cayleyColorStep A.colorDir ca (blocks j)) := by
            rw [hblock]
      _ = C.equiv.symm (blocks j) + 1 :=
            CycleCoordinate.rank_step C (blocks j)
      _ = cayleyColorStep B.colorDir cb ranks j := by
            simp [cayleyColorStep, torusBasis, ranks,
              torusVertexBlockRankEquiv_apply, blocks, C, j]
  · have hblock :
        torusVertexBlockEquiv a b m
            (x + torusBasis (a * b) m
              (blockIndexEquiv a b (j, A.colorDir ca (blocks j)))) q =
          blocks q := by
      simp [blocks, torusVertexBlockEquiv_add_torusBasis_apply, hq]
    calc
      torusVertexBlockRankEquiv (a := a) (b := b) (m := m) (coordA ca)
          (cayleyColorStep (productCayleyColorDir A B coordA)
            (blockIndexEquiv a b (cb, ca)) x) q =
          C.equiv.symm
            (torusVertexBlockEquiv a b m
              (x + torusBasis (a * b) m
                (blockIndexEquiv a b (j, A.colorDir ca (blocks j)))) q) := by
            simp [torusVertexBlockRankEquiv_apply, cayleyColorStep, C, hdir]
      _ = C.equiv.symm (blocks q) := by rw [hblock]
      _ = cayleyColorStep B.colorDir cb ranks q := by
            simp [cayleyColorStep, torusBasis, ranks,
              torusVertexBlockRankEquiv_apply, blocks, C, j, hq]

theorem productCayleyColorDir_colorHamiltonian
    {a b m : Nat} [NeZero (m ^ a)]
    (A : CayleyDecomposition a m)
    (B : CayleyDecomposition b (m ^ a))
    (coordA :
      ∀ c : TorusColor a, CycleCoordinate (m ^ a) (cayleyColorStep A.colorDir c)) :
    IsCayleyColorHamiltonian (productCayleyColorDir A B coordA) := by
  intro c
  let cb : TorusColor b := ((blockIndexEquiv a b).symm c).1
  let ca : TorusColor a := ((blockIndexEquiv a b).symm c).2
  have hc : blockIndexEquiv a b (cb, ca) = c := by
    simp [cb, ca]
  rw [← hc]
  let E := torusVertexBlockRankEquiv (a := a) (b := b) (m := m) (coordA ca)
  refine single_cycle_of_equiv_conj
    (e := E.symm)
    (f := cayleyColorStep (productCayleyColorDir A B coordA)
      (blockIndexEquiv a b (cb, ca)))
    (g := cayleyColorStep B.colorDir cb)
    (B.colorHamiltonian cb) ?_
  intro y
  simpa [E] using
    productCayleyColorStep_rank A B coordA cb ca (E.symm y)

def productCayleyDecomposition
    {a b m : Nat} [NeZero (m ^ a)]
    (A : CayleyDecomposition a m)
    (B : CayleyDecomposition b (m ^ a))
    (coordA :
      ∀ c : TorusColor a, CycleCoordinate (m ^ a) (cayleyColorStep A.colorDir c)) :
    CayleyDecomposition (a * b) m where
  colorDir := productCayleyColorDir A B coordA
  edgePartition := productCayleyColorDir_edgePartition A B coordA
  colorHamiltonian := productCayleyColorDir_colorHamiltonian A B coordA

theorem cayleyHamiltonDecomposition_product_of_left_coordinates
    {a b m : Nat} [NeZero (m ^ a)]
    (A : CoordinatizedCayleyDecomposition a m)
    (B : CayleyDecomposition b (m ^ a)) :
    CayleyHamiltonDecomposition (a * b) m := by
  exact ⟨productCayleyDecomposition
    A.toCayleyDecomposition B A.cycleCoordinate⟩

theorem cayleyHamiltonDecomposition_product_of_left_coordinatized
    {a b m : Nat}
    (hA : CoordinatizedCayleyHamiltonDecomposition a m)
    (hB : CayleyHamiltonDecomposition b (m ^ a)) :
    CayleyHamiltonDecomposition (a * b) m := by
  rcases hA with ⟨hpow, ⟨A⟩⟩
  rcases hB with ⟨B⟩
  letI : NeZero (m ^ a) := hpow
  exact cayleyHamiltonDecomposition_product_of_left_coordinates A B

end Shared
