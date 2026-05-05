import Mathlib
import RoundComposite.ActiveHall
import Shared.Monodromy
import Shared.TorusCayley

namespace RoundComposite
namespace Concrete
namespace BaseTail

def activeDir (b : Nat) : Fin (b + 1) :=
  Fin.last b

structure Cylinder (b m T : Nat) (packets : List (List Nat)) where
  dir : Fin (b + T) → Shared.TorusVertex (b + 1) m → Fin (b + 1)
  active_card :
    ∀ x : Shared.TorusVertex (b + 1) m,
      ((Finset.univ : Finset (Fin (b + T))).filter
        (fun c => dir c x = activeDir b)).card = T

namespace Cylinder

def active {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (x : Shared.TorusVertex (b + 1) m) : Finset (Fin (b + T)) :=
  (Finset.univ : Finset (Fin (b + T))).filter
    (fun c => Cyl.dir c x = activeDir b)

noncomputable def incidence {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) :
    ActiveHall.Incidence T
      (Shared.TorusVertex (b + 1) m) (Fin (b + T)) where
  active := Cyl.active
  active_card := by
    intro x
    exact Cyl.active_card x

def step {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (c : Fin (b + T)) :
    Shared.TorusVertex (b + 1) m → Shared.TorusVertex (b + 1) m :=
  fun x => x + Shared.torusBasis (b + 1) m (Cyl.dir c x)

end Cylinder

def basePart {b m : Nat}
    (x : Shared.TorusVertex (b + 1) m) : Shared.TorusVertex b m :=
  fun j => x j.castSucc

def activeCoord {b m : Nat}
    (x : Shared.TorusVertex (b + 1) m) : ZMod m :=
  x (activeDir b)

theorem castSucc_ne_activeDir {b : Nat} (i : Fin b) :
    i.castSucc ≠ activeDir b := by
  intro h
  have hv := congrArg Fin.val h
  simp [activeDir] at hv
  omega

theorem activeDir_ne_castSucc {b : Nat} (i : Fin b) :
    activeDir b ≠ i.castSucc :=
  (castSucc_ne_activeDir i).symm

@[simp] theorem basePart_snoc {b m : Nat}
    (x : Shared.TorusVertex b m) (a : ZMod m) :
    basePart (b := b) (m := m) (Fin.snoc x a) = x := by
  funext j
  exact Fin.snoc_castSucc (α := fun _ : Fin (b + 1) => ZMod m) a x j

@[simp] theorem activeCoord_snoc {b m : Nat}
    (x : Shared.TorusVertex b m) (a : ZMod m) :
    activeCoord (b := b) (m := m) (Fin.snoc x a) = a := by
  simp [activeCoord, activeDir]

@[simp] theorem snoc_basePart_activeCoord {b m : Nat}
    (x : Shared.TorusVertex (b + 1) m) :
    Fin.snoc (basePart x) (activeCoord x) = x := by
  exact Fin.snoc_init_self x

@[simp] theorem basePart_add_castSucc {b m : Nat}
    (x : Shared.TorusVertex (b + 1) m) (i : Fin b) :
    basePart (x + Shared.torusBasis (b + 1) m i.castSucc) =
      basePart x + Shared.torusBasis b m i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [basePart, Shared.torusBasis]
  · have hne : j.castSucc ≠ i.castSucc := by
      intro h
      exact hji (Fin.ext (by simpa using congrArg Fin.val h))
    simp [basePart, Shared.torusBasis, hji, hne]

@[simp] theorem activeCoord_add_castSucc {b m : Nat}
    (x : Shared.TorusVertex (b + 1) m) (i : Fin b) :
    activeCoord (x + Shared.torusBasis (b + 1) m i.castSucc) =
      activeCoord x := by
  have hne : activeDir b ≠ i.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp [activeDir] at hv
    omega
  simp [activeCoord, Shared.torusBasis, hne]

@[simp] theorem basePart_add_activeDir {b m : Nat}
    (x : Shared.TorusVertex (b + 1) m) :
    basePart (x + Shared.torusBasis (b + 1) m (activeDir b)) =
      basePart x := by
  funext j
  have hne : j.castSucc ≠ activeDir b := by
    intro h
    have hv := congrArg Fin.val h
    simp [activeDir] at hv
    omega
  simp [basePart, Shared.torusBasis, hne]

@[simp] theorem activeCoord_add_activeDir {b m : Nat}
    (x : Shared.TorusVertex (b + 1) m) :
    activeCoord (x + Shared.torusBasis (b + 1) m (activeDir b)) =
      activeCoord x + 1 := by
  simp [activeCoord, Shared.torusBasis]

def baseActiveEquiv (b m : Nat) :
    Shared.TorusVertex (b + 1) m ≃
      Shared.TorusVertex b m × ZMod m where
  toFun x := (basePart x, activeCoord x)
  invFun y := Fin.snoc y.1 y.2
  left_inv := by
    intro x
    exact snoc_basePart_activeCoord x
  right_inv := by
    intro y
    rcases y with ⟨x, a⟩
    simp [activeCoord, activeDir]

noncomputable def baseActiveRankEquiv {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f) :
    Shared.TorusVertex (b + 1) m ≃ ZMod N × ZMod m where
  toFun x := (C.equiv.symm (basePart x), activeCoord x)
  invFun y := Fin.snoc (C.equiv y.1) y.2
  left_inv := by
    intro x
    simp
  right_inv := by
    intro y
    rcases y with ⟨z, a⟩
    simp

@[simp] theorem baseActiveRankEquiv_apply {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f)
    (x : Shared.TorusVertex (b + 1) m) :
    baseActiveRankEquiv C x =
      (C.equiv.symm (basePart x), activeCoord x) := by
  rfl

@[simp] theorem baseActiveRankEquiv_symm_apply {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f)
    (y : ZMod N × ZMod m) :
    (baseActiveRankEquiv C).symm y =
      Fin.snoc (C.equiv y.1) y.2 := by
  rfl

@[simp] theorem baseActiveRankEquiv_snoc {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f)
    (u : Shared.TorusVertex b m) (a : ZMod m) :
    baseActiveRankEquiv C (Fin.snoc u a) =
      (C.equiv.symm u, a) := by
  simp [baseActiveRankEquiv]

theorem baseActiveRankEquiv_snoc_step {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f)
    (u : Shared.TorusVertex b m) (a : ZMod m) :
    baseActiveRankEquiv C (Fin.snoc (f u) a) =
      (C.equiv.symm u + 1, a) := by
  simp [Shared.CycleCoordinate.rank_step C u]

theorem baseActiveRankEquiv_active_step {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f)
    (u : Shared.TorusVertex b m) (a : ZMod m) :
    baseActiveRankEquiv C (Fin.snoc u (a + 1)) =
      (C.equiv.symm u, a + 1) := by
  simp [baseActiveRankEquiv]

theorem baseActiveRankEquiv_add_castSucc_of_step
    {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f)
    (u : Shared.TorusVertex b m) (a : ZMod m) (i : Fin b)
    (hstep : f u = u + Shared.torusBasis b m i) :
    baseActiveRankEquiv C
        (Fin.snoc u a + Shared.torusBasis (b + 1) m i.castSucc) =
      (C.equiv.symm u + 1, a) := by
  calc
    baseActiveRankEquiv C
        (Fin.snoc u a + Shared.torusBasis (b + 1) m i.castSucc)
        =
      (C.equiv.symm (u + Shared.torusBasis b m i), a) := by
        simp [baseActiveRankEquiv]
    _ = (C.equiv.symm (f u), a) := by
        rw [← hstep]
    _ = (C.equiv.symm u + 1, a) := by
        rw [Shared.CycleCoordinate.rank_step C u]

theorem baseActiveRankEquiv_add_activeDir
    {b m N : Nat} [NeZero N]
    {f : Shared.TorusVertex b m → Shared.TorusVertex b m}
    (C : Shared.CycleCoordinate N f)
    (u : Shared.TorusVertex b m) (a : ZMod m) :
    baseActiveRankEquiv C
        (Fin.snoc u a + Shared.torusBasis (b + 1) m (activeDir b)) =
      (C.equiv.symm u, a + 1) := by
  simp [baseActiveRankEquiv]

def ordinaryExpandedDir {b T : Nat}
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) : Fin (b + T) :=
  ⟨i.val, by
    have hlt : i.val < b := by
      by_contra hnot
      have hv : i.val = b := by omega
      exact hi (by
        apply Fin.ext
        simp [activeDir, hv])
    omega⟩

def tailExpandedDir (b : Nat) {T : Nat} (σ : Fin T) : Fin (b + T) :=
  ⟨b + σ.val, by omega⟩

def ordinaryBaseDirOfExpandedDir {b T : Nat}
    (i : Fin (b + T)) (hi : i.val < b) : Fin (b + 1) :=
  ⟨i.val, by omega⟩

def tailSymbolOfExpandedDir {b T : Nat}
    (i : Fin (b + T)) (hi : b ≤ i.val) : Fin T :=
  ⟨i.val - b, by omega⟩

theorem ordinaryBaseDirOfExpandedDir_ne_active {b T : Nat}
    (i : Fin (b + T)) (hi : i.val < b) :
    ordinaryBaseDirOfExpandedDir i hi ≠ activeDir b := by
  intro h
  have hv := congrArg Fin.val h
  simp [ordinaryBaseDirOfExpandedDir, activeDir] at hv
  omega

theorem ordinaryExpandedDir_val_lt {b T : Nat}
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    (ordinaryExpandedDir (T := T) i hi).val < b := by
  have hval : (ordinaryExpandedDir (T := T) i hi).val = i.val := rfl
  by_contra hnot
  rw [hval] at hnot
  have hv : i.val = b := by omega
  exact hi (by
    apply Fin.ext
    simp [activeDir, hv])

theorem ordinaryExpandedDir_of_ordinaryBaseDir {b T : Nat}
    (i : Fin (b + T)) (hi : i.val < b) :
    ordinaryExpandedDir
        (ordinaryBaseDirOfExpandedDir i hi)
        (ordinaryBaseDirOfExpandedDir_ne_active i hi) = i := by
  apply Fin.ext
  simp [ordinaryExpandedDir, ordinaryBaseDirOfExpandedDir]

theorem tailExpandedDir_val_ge (b : Nat) {T : Nat} (σ : Fin T) :
    b ≤ (tailExpandedDir b σ).val := by
  simp [tailExpandedDir]

theorem tailExpandedDir_of_tailSymbol {b T : Nat}
    (i : Fin (b + T)) (hi : b ≤ i.val) :
    tailExpandedDir b (tailSymbolOfExpandedDir i hi) = i := by
  apply Fin.ext
  simp [tailExpandedDir, tailSymbolOfExpandedDir]
  omega

theorem tailExpandedDir_injective {b T : Nat} :
    Function.Injective (tailExpandedDir b : Fin T → Fin (b + T)) := by
  intro σ τ h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [tailExpandedDir] at hv
  omega

theorem ordinaryExpandedDir_ne_tailExpandedDir {b T : Nat}
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) (σ : Fin T) :
    ordinaryExpandedDir (T := T) i hi ≠ tailExpandedDir b σ := by
  intro h
  have hlt := ordinaryExpandedDir_val_lt (T := T) i hi
  have hge := tailExpandedDir_val_ge b σ
  rw [h] at hlt
  omega

def collapseVertex (b m T : Nat)
    (x : Shared.TorusVertex (b + T) m) :
    Shared.TorusVertex (b + 1) m :=
  fun i =>
    if hi : i.val < b then
      x ⟨i.val, by omega⟩
    else
      ∑ σ : Fin T, x (tailExpandedDir b σ)

def collapseFiberInit (b m n : Nat)
    (x : Shared.TorusVertex (b + (n + 1)) m) : Fin n → ZMod m :=
  fun σ => x (tailExpandedDir b σ.castSucc)

def collapseFiberAssemble (b m n : Nat)
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m) :
    Shared.TorusVertex (b + (n + 1)) m :=
  fun j =>
    if hOrd : j.val < b then
      y ⟨j.val, by omega⟩
    else if hInit : j.val < b + n then
      z ⟨j.val - b, by omega⟩
    else
      y (activeDir b) - ∑ σ : Fin n, z σ

noncomputable def collapseVertexFiberEquiv (b m n : Nat) :
    Shared.TorusVertex (b + (n + 1)) m ≃
      Shared.TorusVertex (b + 1) m × (Fin n → ZMod m) where
  toFun x := (collapseVertex b m (n + 1) x, collapseFiberInit b m n x)
  invFun p := collapseFiberAssemble b m n p.1 p.2
  left_inv := by
    classical
    intro x
    funext j
    by_cases hOrd : j.val < b
    · have hj : (⟨j.val, by omega⟩ : Fin (b + (n + 1))) = j := by
        ext
        rfl
      simp [collapseFiberAssemble, collapseVertex, hOrd, hj]
    · by_cases hInit : j.val < b + n
      · let σ : Fin n := ⟨j.val - b, by omega⟩
        have htail : tailExpandedDir b σ.castSucc = j := by
          ext
          simp [tailExpandedDir, σ]
          omega
        simpa [collapseFiberAssemble, collapseFiberInit, hOrd, hInit, σ]
          using congrArg x htail
      · have hjval : j.val = b + n := by omega
        have hlast : tailExpandedDir b (Fin.last n) = j := by
          ext
          simp [tailExpandedDir, hjval]
        have hsum :
            (∑ τ : Fin (n + 1), x (tailExpandedDir b τ)) =
              (∑ σ : Fin n, x (tailExpandedDir b σ.castSucc)) +
                x (tailExpandedDir b (Fin.last n)) := by
          rw [Fin.sum_univ_castSucc]
        have hActiveOrd : ¬ (activeDir b).val < b := by
          simp [activeDir]
        have hLastOrd : ¬ (tailExpandedDir b (Fin.last n)).val < b := by
          simp [tailExpandedDir]
        have hLastInit :
            ¬ (tailExpandedDir b (Fin.last n)).val < b + n := by
          simp [tailExpandedDir]
        rw [← hlast]
        simp [collapseFiberAssemble, collapseVertex, collapseFiberInit,
          hsum, hActiveOrd, hLastOrd, hLastInit, sub_eq_add_neg]
  right_inv := by
    classical
    intro p
    rcases p with ⟨y, z⟩
    ext i
    · by_cases hi : i.val < b
      · have hi' : (⟨i.val, by omega⟩ : Fin (b + (n + 1))) =
            ⟨i.val, by omega⟩ := rfl
        simp [collapseFiberAssemble, collapseVertex, hi]
      · have hactive : i = activeDir b := by
          ext
          simp [activeDir]
          omega
        subst i
        have hsum :
            (∑ τ : Fin (n + 1),
                collapseFiberAssemble b m n y z (tailExpandedDir b τ)) =
              (∑ σ : Fin n, z σ) +
                (y (activeDir b) - ∑ σ : Fin n, z σ) := by
          rw [Fin.sum_univ_castSucc]
          congr 1
          · apply Finset.sum_congr rfl
            intro σ _hσ
            have hOrd : ¬ (tailExpandedDir b σ.castSucc).val < b := by
              simp [tailExpandedDir]
            have hInit : (tailExpandedDir b σ.castSucc).val < b + n := by
              simp [tailExpandedDir]
            have hidx :
                ((tailExpandedDir b σ.castSucc).val - b) = σ.val := by
              simp [tailExpandedDir]
            simp [collapseFiberAssemble, hOrd, hInit, hidx]
          · have hOrd : ¬ (tailExpandedDir b (Fin.last n)).val < b := by
              simp [tailExpandedDir]
            have hInit :
                ¬ (tailExpandedDir b (Fin.last n)).val < b + n := by
              simp [tailExpandedDir]
            simp [collapseFiberAssemble, hOrd, hInit]
        simp [collapseVertex, activeDir, hsum, sub_eq_add_neg]
    · have hOrd : ¬ (tailExpandedDir b i.castSucc).val < b := by
        simp [tailExpandedDir]
      have hInit : (tailExpandedDir b i.castSucc).val < b + n := by
        simp [tailExpandedDir]
      have hidx : ((tailExpandedDir b i.castSucc).val - b) = i.val := by
        simp [tailExpandedDir]
      simp [collapseFiberAssemble, collapseFiberInit, hOrd, hInit, hidx]

theorem collapseVertex_add_ordinaryExpandedDir {b m T : Nat}
    (x : Shared.TorusVertex (b + T) m)
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    collapseVertex b m T
        (x + Shared.torusBasis (b + T) m (ordinaryExpandedDir i hi))
      =
    collapseVertex b m T x + Shared.torusBasis (b + 1) m i := by
  classical
  funext j
  by_cases hj : j.val < b
  · by_cases hji : j = i
    · subst i
      simp [collapseVertex, hj, Shared.torusBasis, ordinaryExpandedDir]
    · have hne :
          (⟨j.val, by omega⟩ : Fin (b + T)) ≠
            ordinaryExpandedDir i hi := by
        intro h
        exact hji (by
          apply Fin.ext
          simpa [ordinaryExpandedDir] using congrArg Fin.val h)
      simp [collapseVertex, hj, Shared.torusBasis, hji, hne]
  · have hjval : j.val = b := by omega
    have hji : j ≠ i := by
      intro h
      have hv : i.val = b := by
        rw [← congrArg Fin.val h]
        exact hjval
      exact hi (by
        apply Fin.ext
        simp [activeDir, hv])
    have hzero :
        (∑ σ : Fin T,
          Shared.torusBasis (b + T) m
            (ordinaryExpandedDir i hi) (tailExpandedDir b σ)) = 0 := by
      apply Finset.sum_eq_zero
      intro σ _hσ
      have hne :
          tailExpandedDir b σ ≠ ordinaryExpandedDir i hi := by
        exact (ordinaryExpandedDir_ne_tailExpandedDir i hi σ).symm
      simp [Shared.torusBasis, hne]
    calc
      collapseVertex b m T
          (x + Shared.torusBasis (b + T) m (ordinaryExpandedDir i hi)) j
          =
        ∑ σ : Fin T,
          (x + Shared.torusBasis (b + T) m
            (ordinaryExpandedDir i hi)) (tailExpandedDir b σ) := by
          simp [collapseVertex, hj]
      _ =
        (∑ σ : Fin T, x (tailExpandedDir b σ)) +
          ∑ σ : Fin T,
            Shared.torusBasis (b + T) m
              (ordinaryExpandedDir i hi) (tailExpandedDir b σ) := by
          simp [Pi.add_apply, Finset.sum_add_distrib]
      _ = ∑ σ : Fin T, x (tailExpandedDir b σ) := by
          rw [hzero, add_zero]
      _ =
        (collapseVertex b m T x + Shared.torusBasis (b + 1) m i) j := by
          simp [collapseVertex, hj, Shared.torusBasis, hji, Pi.add_apply]

theorem collapseVertex_add_tailExpandedDir {b m T : Nat}
    (x : Shared.TorusVertex (b + T) m) (σ : Fin T) :
    collapseVertex b m T
        (x + Shared.torusBasis (b + T) m (tailExpandedDir b σ))
      =
    collapseVertex b m T x + Shared.torusBasis (b + 1) m (activeDir b) := by
  classical
  funext j
  by_cases hj : j.val < b
  · have hne :
        (⟨j.val, by omega⟩ : Fin (b + T)) ≠ tailExpandedDir b σ := by
      intro h
      have hv := congrArg Fin.val h
      simp [tailExpandedDir] at hv
      omega
    have hnotActive : j ≠ activeDir b := by
      intro h
      have hv := congrArg Fin.val h
      simp [activeDir] at hv
      omega
    simp [collapseVertex, hj, Shared.torusBasis, hne, hnotActive]
  · have hjActive : j = activeDir b := by
      apply Fin.ext
      simp [activeDir]
      omega
    have hsum :
        (∑ τ : Fin T,
          Shared.torusBasis (b + T) m
            (tailExpandedDir b σ) (tailExpandedDir b τ)) = 1 := by
      rw [Finset.sum_eq_single σ]
      · simp [Shared.torusBasis]
      · intro τ _hτ hτσ
        have hne : tailExpandedDir b τ ≠ tailExpandedDir b σ := by
          intro h
          exact hτσ (tailExpandedDir_injective h)
        simp [Shared.torusBasis, hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ σ))
    subst j
    calc
      collapseVertex b m T
          (x + Shared.torusBasis (b + T) m (tailExpandedDir b σ))
          (activeDir b)
          =
        ∑ τ : Fin T,
          (x + Shared.torusBasis (b + T) m
            (tailExpandedDir b σ)) (tailExpandedDir b τ) := by
          simp [collapseVertex, activeDir]
      _ =
        (∑ τ : Fin T, x (tailExpandedDir b τ)) +
          ∑ τ : Fin T,
            Shared.torusBasis (b + T) m
              (tailExpandedDir b σ) (tailExpandedDir b τ) := by
          simp [Pi.add_apply, Finset.sum_add_distrib]
      _ = (∑ τ : Fin T, x (tailExpandedDir b τ)) + 1 := by
          rw [hsum]
      _ =
        (collapseVertex b m T x +
          Shared.torusBasis (b + 1) m (activeDir b)) (activeDir b) := by
          simp [collapseVertex, activeDir, Shared.torusBasis, Pi.add_apply]

theorem collapseFiberInit_add_ordinaryExpandedDir {b m n : Nat}
    (x : Shared.TorusVertex (b + (n + 1)) m)
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    collapseFiberInit b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (ordinaryExpandedDir (T := n + 1) i hi))
      =
    collapseFiberInit b m n x := by
  funext σ
  have hne :
      tailExpandedDir b σ.castSucc ≠
        ordinaryExpandedDir (T := n + 1) i hi :=
    (ordinaryExpandedDir_ne_tailExpandedDir i hi σ.castSucc).symm
  simp [collapseFiberInit, Shared.torusBasis, hne]

theorem collapseVertexFiberEquiv_add_ordinaryExpandedDir {b m n : Nat}
    (x : Shared.TorusVertex (b + (n + 1)) m)
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (ordinaryExpandedDir (T := n + 1) i hi))
      =
    (collapseVertex b m (n + 1) x +
        Shared.torusBasis (b + 1) m i,
      collapseFiberInit b m n x) := by
  apply Prod.ext
  · exact collapseVertex_add_ordinaryExpandedDir x i hi
  · exact collapseFiberInit_add_ordinaryExpandedDir x i hi

theorem collapseFiberInit_add_tailExpandedDir_castSucc {b m n : Nat}
    (x : Shared.TorusVertex (b + (n + 1)) m) (σ : Fin n) :
    collapseFiberInit b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b σ.castSucc))
      =
    fun τ : Fin n =>
      collapseFiberInit b m n x τ + if τ = σ then (1 : ZMod m) else 0 := by
  funext τ
  by_cases hτσ : τ = σ
  · subst τ
    simp [collapseFiberInit, Shared.torusBasis]
  · have hne :
        tailExpandedDir b τ.castSucc ≠ tailExpandedDir b σ.castSucc := by
      intro h
      exact hτσ (Fin.ext (by
        have hv := congrArg Fin.val (tailExpandedDir_injective h)
        simpa using hv))
    simp [collapseFiberInit, Shared.torusBasis, hτσ, hne]

theorem collapseVertexFiberEquiv_add_tailExpandedDir_castSucc {b m n : Nat}
    (x : Shared.TorusVertex (b + (n + 1)) m) (σ : Fin n) :
    collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b σ.castSucc))
      =
    (collapseVertex b m (n + 1) x +
        Shared.torusBasis (b + 1) m (activeDir b),
      fun τ : Fin n =>
        collapseFiberInit b m n x τ +
          if τ = σ then (1 : ZMod m) else 0) := by
  apply Prod.ext
  · exact collapseVertex_add_tailExpandedDir x σ.castSucc
  · exact collapseFiberInit_add_tailExpandedDir_castSucc x σ

theorem collapseFiberInit_add_tailExpandedDir_last {b m n : Nat}
    (x : Shared.TorusVertex (b + (n + 1)) m) :
    collapseFiberInit b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b (Fin.last n)))
      =
    collapseFiberInit b m n x := by
  funext σ
  have hne :
      tailExpandedDir b σ.castSucc ≠ tailExpandedDir b (Fin.last n) := by
    intro h
    have hv := congrArg Fin.val h
    simp [tailExpandedDir] at hv
    omega
  simp [collapseFiberInit, Shared.torusBasis, hne]

theorem collapseVertexFiberEquiv_add_tailExpandedDir_last {b m n : Nat}
    (x : Shared.TorusVertex (b + (n + 1)) m) :
    collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b (Fin.last n)))
      =
    (collapseVertex b m (n + 1) x +
        Shared.torusBasis (b + 1) m (activeDir b),
      collapseFiberInit b m n x) := by
  apply Prod.ext
  · exact collapseVertex_add_tailExpandedDir x (Fin.last n)
  · exact collapseFiberInit_add_tailExpandedDir_last x

structure IsCylinder {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) : Prop where
  ordinary_unique :
    ∀ x : Shared.TorusVertex (b + 1) m,
      ∀ i : Fin (b + 1), i ≠ activeDir b →
        ∃! c : Fin (b + T), Cyl.dir c x = i
  color_hamiltonian :
    ∀ c : Fin (b + T), Shared.IsSingleCycleMap (Cyl.step c)
  active_degree_mod :
    ∀ c : Fin (b + T),
      (((Cyl.incidence).colorDegree c : Nat) : ZMod m) = 0

theorem cycleCoordinate_iterate_apply {N : Nat} [NeZero N]
    {α : Type*} {f : α → α}
    (C : Shared.CycleCoordinate N f) (k : Nat) (z : ZMod N) :
    (f^[k]) (C.equiv z) = C.equiv (z + (k : ZMod N)) := by
  induction k generalizing z with
  | zero =>
      simp
  | succ k ih =>
      calc
        (f^[k + 1]) (C.equiv z) =
            f ((f^[k]) (C.equiv z)) := by
              rw [Function.iterate_succ_apply']
        _ = f (C.equiv (z + (k : ZMod N))) := by
              rw [ih]
        _ = C.equiv ((z + (k : ZMod N)) + 1) := by
              rw [← C.step]
        _ = C.equiv (z + ((k + 1 : Nat) : ZMod N)) := by
              congr 1
              norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
                add_left_comm]

structure CylinderBaseCycleData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  base : Fin (b + T) → Shared.TorusVertex (b + 1) m
  period : Fin (b + T) → Nat
  period_eq : ∀ c : Fin (b + T), period c = m ^ (b + 1)
  return_base :
    ∀ c : Fin (b + T), ((Cyl.step c)^[period c]) (base c) = base c
  base_cover :
    ∀ c : Fin (b + T),
      ∀ y : Shared.TorusVertex (b + 1) m,
        ∃ k : Nat, k < period c ∧ ((Cyl.step c)^[k]) (base c) = y

theorem cylinderBaseCycleData_of_isCylinder
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} (hCyl : IsCylinder Cyl) :
    Nonempty (CylinderBaseCycleData Cyl) := by
  classical
  by_cases hm1 : m = 1
  · subst m
    refine ⟨{
      base := fun _ => default
      period := fun _ => 1
      period_eq := ?_
      return_base := ?_
      base_cover := ?_
    }⟩
    · intro c
      simp
    · intro c
      exact Subsingleton.elim _ _
    · intro c y
      refine ⟨0, by omega, ?_⟩
      exact Subsingleton.elim _ _
  · have hmgt : 1 < m := by
      have hm0 : m ≠ 0 := NeZero.ne m
      omega
    have hperiod : 1 < m ^ (b + 1) :=
      one_lt_pow' hmgt (by omega)
    haveI : NeZero (m ^ (b + 1)) :=
      ⟨pow_ne_zero (b + 1) (NeZero.ne m)⟩
    let C :
        (c : Fin (b + T)) →
          Shared.CycleCoordinate (m ^ (b + 1)) (Cyl.step c) :=
      fun c =>
        Shared.CycleCoordinate.ofFiniteSingleCycle
          (by rw [Shared.card_torusVertex]) hperiod (hCyl.color_hamiltonian c)
    refine ⟨{
      base := fun c => (C c).equiv 0
      period := fun _ => m ^ (b + 1)
      period_eq := ?_
      return_base := ?_
      base_cover := ?_
    }⟩
    · intro c
      rfl
    · intro c
      have hiter :=
        cycleCoordinate_iterate_apply (C c) (m ^ (b + 1))
          (0 : ZMod (m ^ (b + 1)))
      simpa using hiter
    · intro c y
      let z : ZMod (m ^ (b + 1)) := (C c).equiv.symm y
      refine ⟨z.val, ZMod.val_lt z, ?_⟩
      have hiter :=
        cycleCoordinate_iterate_apply (C c) z.val
          (0 : ZMod (m ^ (b + 1)))
      calc
        ((Cyl.step c)^[z.val]) ((C c).equiv 0) =
            (C c).equiv (0 + (z.val : ZMod (m ^ (b + 1)))) := hiter
        _ = y := by
            simp [z]

structure ActiveBlockData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  activeBlock : Fin (b + T) → Nat
  activeBlock_pos : ∀ c : Fin (b + T), 0 < activeBlock c
  activeBlock_lt : ∀ c : Fin (b + T), activeBlock c < m
  activeBlock_coprime : ∀ c : Fin (b + T), Nat.Coprime (activeBlock c) m
  active_degree_eq :
    ∀ c : Fin (b + T),
      (Cyl.incidence).colorDegree c = (m - activeBlock c) * m ^ b

structure MixedExpansionData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  mixed_lower :
    ∀ U : Finset (Fin (b + T)),
      U.Nonempty → U ≠ Finset.univ →
        m ^ b ≤ (Cyl.incidence).mixedCount U

structure MixedLowerWitnessData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  witness :
    ∀ U : Finset (Fin (b + T)),
      U.Nonempty → U ≠ Finset.univ →
        Finset (Shared.TorusVertex (b + 1) m)
  witness_card :
    ∀ U hUne hUuniv, (witness U hUne hUuniv).card = m ^ b
  witness_mixed :
    ∀ U hUne hUuniv,
      ∀ x, x ∈ witness U hUne hUuniv →
        0 < (Cyl.incidence.active x ∩ U).card ∧
          (Cyl.incidence.active x ∩ U).card < T

/--
Phase splitter for one packet over one compressed base color cycle.

For a packet of active block sizes summing to `m`, the splitter chooses exactly
one packet part as the ordinary move at each `(base-rank, active-coordinate)`
state.  The cardinality field records that part `r` is ordinary for
`packet.get r * N` states, and the cycle field is the genuinely hard packet
Hamiltonicity assertion used by the successor cylinder construction.
-/
structure PacketPhaseSplit (N m : Nat) [NeZero N] [NeZero m]
    (packet : List Nat) where
  ordinary : Fin packet.length → ZMod N × ZMod m → Bool
  ordinary_unique :
    ∀ y : ZMod N × ZMod m,
      ∃! r : Fin packet.length, ordinary r y = true
  ordinary_card :
    ∀ r : Fin packet.length,
      ((Finset.univ : Finset (ZMod N × ZMod m)).filter
        (fun y => ordinary r y = true)).card = packet.get r * N
  step_singleCycle :
    ∀ r : Fin packet.length,
      Shared.IsSingleCycleMap
        (fun y : ZMod N × ZMod m =>
          if ordinary r y then (y.1 + 1, y.2) else (y.1, y.2 + 1))

namespace PacketPhaseSplit

theorem ordinary_true_card_at_state {N m : Nat} [NeZero N] [NeZero m]
    {packet : List Nat} (S : PacketPhaseSplit N m packet)
    (y : ZMod N × ZMod m) :
    ((Finset.univ : Finset (Fin packet.length)).filter
      (fun r => S.ordinary r y = true)).card = 1 := by
  classical
  rcases S.ordinary_unique y with ⟨r, hr, huniq⟩
  rw [Finset.card_eq_one]
  refine ⟨r, ?_⟩
  ext s
  constructor
  · intro hs
    simpa using huniq s (Finset.mem_filter.mp hs).2
  · intro hs
    have hs' : s = r := by simpa using Finset.mem_singleton.mp hs
    subst s
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩

theorem ordinary_false_card_at_state {N m : Nat} [NeZero N] [NeZero m]
    {packet : List Nat} (S : PacketPhaseSplit N m packet)
    (y : ZMod N × ZMod m) :
    ((Finset.univ : Finset (Fin packet.length)).filter
      (fun r => S.ordinary r y = false)).card = packet.length - 1 := by
  classical
  have hnot :
      ((Finset.univ : Finset (Fin packet.length)).filter
        (fun r => ¬ S.ordinary r y = true)).card =
      ((Finset.univ : Finset (Fin packet.length)).filter
        (fun r => S.ordinary r y = false)).card := by
    apply congrArg Finset.card
    ext r
    by_cases h : S.ordinary r y <;> simp [h]
  have hsum :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin packet.length)))
      (p := fun r => S.ordinary r y = true)
  rw [hnot, S.ordinary_true_card_at_state y] at hsum
  have hlenpos : 0 < packet.length := by
    rcases S.ordinary_unique y with ⟨r, _hr, _huniq⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le r.val) r.2
  have hsum' :
      1 +
        ((Finset.univ : Finset (Fin packet.length)).filter
          (fun r => S.ordinary r y = false)).card =
        packet.length := by
    simpa using hsum
  have htarget : 1 + (packet.length - 1) = packet.length := by
    omega
  exact Nat.add_left_cancel (hsum'.trans htarget.symm)

theorem ordinary_false_card {N m : Nat} [NeZero N] [NeZero m]
    {packet : List Nat} (S : PacketPhaseSplit N m packet)
    (r : Fin packet.length) (hgetle : packet.get r ≤ m) :
    ((Finset.univ : Finset (ZMod N × ZMod m)).filter
      (fun y => S.ordinary r y = false)).card =
        (m - packet.get r) * N := by
  classical
  have hnot :
      ((Finset.univ : Finset (ZMod N × ZMod m)).filter
        (fun y => ¬ S.ordinary r y = true)).card =
      ((Finset.univ : Finset (ZMod N × ZMod m)).filter
        (fun y => S.ordinary r y = false)).card := by
    apply congrArg Finset.card
    ext y
    by_cases h : S.ordinary r y <;> simp [h]
  have hsum :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod N × ZMod m)))
      (p := fun y => S.ordinary r y = true)
  have htotal :
      (Finset.univ : Finset (ZMod N × ZMod m)).card = m * N := by
    simp [Fintype.card_prod, ZMod.card, Nat.mul_comm]
  rw [hnot, S.ordinary_card r, htotal] at hsum
  have hdecomp :
      packet.get r * N + (m - packet.get r) * N = m * N := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hgetle]
  rw [← hdecomp] at hsum
  exact Nat.add_left_cancel hsum

theorem ordinary_false_card_of_equiv
    {N m : Nat} [NeZero N] [NeZero m]
    {α : Type*} [Fintype α]
    {packet : List Nat} (S : PacketPhaseSplit N m packet)
    (e : α ≃ ZMod N × ZMod m)
    (r : Fin packet.length) (hgetle : packet.get r ≤ m) :
    ((Finset.univ : Finset α).filter
      (fun x => S.ordinary r (e x) = false)).card =
        (m - packet.get r) * N := by
  classical
  let eSub :
      {x : α // S.ordinary r (e x) = false} ≃
        {y : ZMod N × ZMod m // S.ordinary r y = false} :=
  {
    toFun := fun x => ⟨e x.1, x.2⟩
    invFun := fun y => ⟨e.symm y.1, by simpa using y.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      simp
    right_inv := by
      intro y
      apply Subtype.ext
      simp
  }
  have hα :
      Fintype.card {x : α // S.ordinary r (e x) = false} =
      ((Finset.univ : Finset α).filter
        (fun x => S.ordinary r (e x) = false)).card := by
    exact Fintype.card_subtype _
  have hy :
      Fintype.card {y : ZMod N × ZMod m // S.ordinary r y = false} =
      ((Finset.univ : Finset (ZMod N × ZMod m)).filter
        (fun y => S.ordinary r y = false)).card := by
    exact Fintype.card_subtype _
  rw [← hα, Fintype.card_congr eSub, hy]
  exact S.ordinary_false_card r hgetle

end PacketPhaseSplit

def packetPhase {N m : Nat} [NeZero N] [NeZero m] (hdiv : m ∣ N) :
    ZMod N × ZMod m → ZMod m :=
  fun y => ZMod.castHom hdiv (ZMod m) y.1 + y.2

theorem packetPhase_step_first {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (y : ZMod N × ZMod m) :
    packetPhase hdiv (y.1 + 1, y.2) = packetPhase hdiv y + 1 := by
  dsimp [packetPhase]
  rw [ZMod.cast_add (R := ZMod m) hdiv y.1 1]
  rw [ZMod.cast_one (R := ZMod m) hdiv]
  abel_nf

theorem packetPhase_step_second {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (y : ZMod N × ZMod m) :
    packetPhase hdiv (y.1, y.2 + 1) = packetPhase hdiv y + 1 := by
  dsimp [packetPhase]
  abel

def packetPhaseFiberEquiv {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (φ : ZMod m) :
    ZMod N ≃ {y : ZMod N × ZMod m // packetPhase hdiv y = φ} where
  toFun x :=
    ⟨(x, φ - ZMod.castHom hdiv (ZMod m) x), by
      dsimp [packetPhase]
      abel⟩
  invFun y := y.1.1
  left_inv x := rfl
  right_inv y := by
    rcases y with ⟨⟨x, z⟩, hθ⟩
    apply Subtype.ext
    change (x, φ - ZMod.castHom hdiv (ZMod m) x) = (x, z)
    apply Prod.ext
    · rfl
    · dsimp [packetPhase] at hθ
      rw [← hθ]
      rw [ZMod.castHom_apply]
      abel

theorem packetPhase_fiber_card {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (φ : ZMod m) :
    ((Finset.univ : Finset (ZMod N × ZMod m)).filter
      (fun y => packetPhase hdiv y = φ)).card = N := by
  have hsub :
      Fintype.card
        {y : ZMod N × ZMod m // packetPhase hdiv y = φ} =
        ((Finset.univ : Finset (ZMod N × ZMod m)).filter
          (fun y => packetPhase hdiv y = φ)).card := by
    exact Fintype.card_subtype _
  have hcongr :
      Fintype.card (ZMod N) =
        Fintype.card
          {y : ZMod N × ZMod m // packetPhase hdiv y = φ} :=
    Fintype.card_congr (packetPhaseFiberEquiv hdiv φ)
  rw [← hsub, ← hcongr]
  exact ZMod.card N

def packetPhasePreimageEquiv {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (S : Finset (ZMod m)) :
    ZMod N × {φ : ZMod m // φ ∈ S} ≃
      {y : ZMod N × ZMod m // packetPhase hdiv y ∈ S} where
  toFun x :=
    ⟨(x.1, x.2.1 - ZMod.castHom hdiv (ZMod m) x.1), by
      dsimp [packetPhase]
      convert x.2.2 using 1
      abel⟩
  invFun y :=
    (y.1.1, ⟨packetPhase hdiv y.1, y.2⟩)
  left_inv x := by
    rcases x with ⟨x, φ⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [packetPhase]
      abel_nf
  right_inv y := by
    rcases y with ⟨⟨x, z⟩, hS⟩
    apply Subtype.ext
    change (x, packetPhase hdiv (x, z) -
        ZMod.castHom hdiv (ZMod m) x) = (x, z)
    apply Prod.ext
    · rfl
    · dsimp [packetPhase]
      abel_nf

theorem packetPhase_preimage_card {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (S : Finset (ZMod m)) :
    ((Finset.univ : Finset (ZMod N × ZMod m)).filter
      (fun y => packetPhase hdiv y ∈ S)).card = S.card * N := by
  have hsub :
      Fintype.card
        {y : ZMod N × ZMod m // packetPhase hdiv y ∈ S} =
        ((Finset.univ : Finset (ZMod N × ZMod m)).filter
          (fun y => packetPhase hdiv y ∈ S)).card := by
    exact Fintype.card_subtype _
  have hcongr :
      Fintype.card (ZMod N × {φ : ZMod m // φ ∈ S}) =
        Fintype.card
          {y : ZMod N × ZMod m // packetPhase hdiv y ∈ S} :=
    Fintype.card_congr (packetPhasePreimageEquiv hdiv S)
  rw [← hsub, ← hcongr]
  simp [Fintype.card_prod, ZMod.card, Fintype.card_subtype,
    Nat.mul_comm]

def packetPrefixLo (packet : List Nat) (r : Fin packet.length) : Nat :=
  (packet.take r.val).sum

def packetPrefixHi (packet : List Nat) (r : Fin packet.length) : Nat :=
  (packet.take (r.val + 1)).sum

def packetPrefixInterval (packet : List Nat) (r : Fin packet.length) :
    Finset Nat :=
  Finset.Ico (packetPrefixLo packet r) (packetPrefixHi packet r)

theorem packetPrefixHi_eq_lo_add_get
    (packet : List Nat) (r : Fin packet.length) :
    packetPrefixHi packet r =
      packetPrefixLo packet r + packet.get r := by
  simp [packetPrefixHi, packetPrefixLo,
    List.sum_take_succ packet r.val r.isLt]

theorem packetPrefixInterval_card
    (packet : List Nat) (r : Fin packet.length) :
    (packetPrefixInterval packet r).card = packet.get r := by
  rw [packetPrefixInterval, Nat.card_Ico,
    packetPrefixHi_eq_lo_add_get]
  omega

theorem packetPrefixHi_le_sum
    (packet : List Nat) (r : Fin packet.length) :
    packetPrefixHi packet r ≤ packet.sum := by
  dsimp [packetPrefixHi]
  have h :=
    List.sum_take_add_sum_drop packet (r.val + 1)
  omega

theorem packetPrefixHi_le_of_sum_eq
    {packet : List Nat} {m : Nat} (hsum : packet.sum = m)
    (r : Fin packet.length) :
    packetPrefixHi packet r ≤ m := by
  rw [← hsum]
  exact packetPrefixHi_le_sum packet r

theorem packetPrefixInterval_mem_lt_sum
    {packet : List Nat} {r : Fin packet.length} {q : Nat}
    (hq : q ∈ packetPrefixInterval packet r) :
    q < packet.sum := by
  have hlt : q < packetPrefixHi packet r := by
    have hmem :
        packetPrefixLo packet r ≤ q ∧ q < packetPrefixHi packet r := by
      simpa [packetPrefixInterval] using hq
    exact hmem.2
  exact lt_of_lt_of_le hlt (packetPrefixHi_le_sum packet r)

theorem packetPrefixInterval_existsUnique_nat
    {packet : List Nat}
    (hpos : ∀ a, a ∈ packet → 0 < a) :
    ∀ q : Nat, q < packet.sum →
      ∃! r : Fin packet.length, q ∈ packetPrefixInterval packet r := by
  induction packet with
  | nil =>
      intro q hq
      simp at hq
  | cons a tail ih =>
      intro q hq
      have ha : 0 < a := hpos a (by simp)
      have htailpos : ∀ b, b ∈ tail → 0 < b := by
        intro b hb
        exact hpos b (by simp [hb])
      by_cases hqa : q < a
      · let r0 : Fin (a :: tail).length := ⟨0, by simp⟩
        refine ⟨r0, ?_, ?_⟩
        · simp [packetPrefixInterval, packetPrefixLo, packetPrefixHi, r0,
            hqa]
        · intro r hr
          apply Fin.ext
          rcases r with ⟨n, hn⟩
          cases n with
          | zero =>
              rfl
          | succ n =>
              have hmem :
                  packetPrefixLo (a :: tail) ⟨n + 1, hn⟩ ≤ q ∧
                    q < packetPrefixHi (a :: tail) ⟨n + 1, hn⟩ := by
                simpa [packetPrefixInterval] using hr
              have hle : a ≤ q := by
                have hle' : a + (tail.take n).sum ≤ q := by
                  simpa [packetPrefixLo] using hmem.1
                omega
              omega
      · have haq : a ≤ q := Nat.le_of_not_gt hqa
        have hqtail : q - a < tail.sum := by
          simp at hq
          omega
        rcases ih htailpos (q - a) hqtail with ⟨s, hs, huniq⟩
        let r : Fin (a :: tail).length :=
          ⟨s.val + 1, by
            simp [s.isLt]⟩
        refine ⟨r, ?_, ?_⟩
        · have hsmem :
              packetPrefixLo tail s ≤ q - a ∧
                q - a < packetPrefixHi tail s := by
            simpa [packetPrefixInterval] using hs
          have hlo : a + packetPrefixLo tail s ≤ q := by omega
          have hhi : q < a + packetPrefixHi tail s := by omega
          simpa [packetPrefixInterval, packetPrefixLo, packetPrefixHi, r]
            using And.intro hlo hhi
        · intro r' hr'
          rcases r' with ⟨n, hn⟩
          cases n with
          | zero =>
              have hmem :
                  packetPrefixLo (a :: tail) ⟨0, hn⟩ ≤ q ∧
                    q < packetPrefixHi (a :: tail) ⟨0, hn⟩ := by
                simpa [packetPrefixInterval] using hr'
              have hlt : q < a := by
                simpa [packetPrefixHi, packetPrefixLo] using hmem.2
              omega
          | succ n =>
              have hn_tail : n < tail.length := by
                simpa using hn
              let s' : Fin tail.length := ⟨n, hn_tail⟩
              have hmem :
                  packetPrefixLo (a :: tail) ⟨n + 1, hn⟩ ≤ q ∧
                    q < packetPrefixHi (a :: tail) ⟨n + 1, hn⟩ := by
                simpa [packetPrefixInterval] using hr'
              have hs' : q - a ∈ packetPrefixInterval tail s' := by
                have hlo : packetPrefixLo tail s' ≤ q - a := by
                  have hle' : a + packetPrefixLo tail s' ≤ q := by
                    simpa [packetPrefixLo, s'] using hmem.1
                  omega
                have hhi : q - a < packetPrefixHi tail s' := by
                  have hlt' : q < a + packetPrefixHi tail s' := by
                    simpa [packetPrefixHi, s'] using hmem.2
                  omega
                simpa [packetPrefixInterval] using And.intro hlo hhi
              have hs_eq : s' = s := huniq s' hs'
              have hn_eq : n = s.val := by
                simpa [s'] using congrArg Fin.val hs_eq
              apply Fin.ext
              simp [r, hn_eq]

def packetPrefixPhaseSet (m : Nat)
    (packet : List Nat) (r : Fin packet.length) : Finset (ZMod m) :=
  (packetPrefixInterval packet r).image
    (fun q : Nat => (q : ZMod m))

theorem packetPrefixPhaseSet_existsUnique
    {m : Nat} [NeZero m] {packet : List Nat}
    (hsum : packet.sum = m)
    (hpos : ∀ a, a ∈ packet → 0 < a) :
    ∀ φ : ZMod m, ∃! r : Fin packet.length,
      φ ∈ packetPrefixPhaseSet m packet r := by
  intro φ
  have hφlt : φ.val < packet.sum := by
    rw [hsum]
    exact ZMod.val_lt φ
  rcases packetPrefixInterval_existsUnique_nat hpos φ.val hφlt with
    ⟨r, hr, huniq⟩
  refine ⟨r, ?_, ?_⟩
  · change φ ∈ (packetPrefixInterval packet r).image
      (fun q : Nat => (q : ZMod m))
    exact Finset.mem_image.mpr
      ⟨φ.val, hr, ZMod.natCast_zmod_val φ⟩
  · intro s hs
    have hs_interval : φ.val ∈ packetPrefixInterval packet s := by
      change φ ∈ (packetPrefixInterval packet s).image
        (fun q : Nat => (q : ZMod m)) at hs
      rcases Finset.mem_image.mp hs with ⟨q, hq, hqφ⟩
      have hq_lt : q < m := by
        rw [← hsum]
        exact packetPrefixInterval_mem_lt_sum hq
      have hq_eq : q = φ.val := by
        apply Nat.ModEq.eq_of_lt_of_lt
          ((ZMod.natCast_eq_natCast_iff q φ.val m).mp ?_)
          hq_lt (ZMod.val_lt φ)
        rw [hqφ, ZMod.natCast_zmod_val]
      simpa [hq_eq] using hq
    exact huniq s hs_interval

theorem packetPrefixPhaseSet_card
    {m : Nat} {packet : List Nat} (hsum : packet.sum = m)
    (r : Fin packet.length) :
    (packetPrefixPhaseSet m packet r).card = packet.get r := by
  rw [packetPrefixPhaseSet]
  rw [Finset.card_image_of_injOn]
  · exact packetPrefixInterval_card packet r
  · intro a ha b hb hab
    have ha_lt : a < m := by
      rw [← hsum]
      exact packetPrefixInterval_mem_lt_sum ha
    have hb_lt : b < m := by
      rw [← hsum]
      exact packetPrefixInterval_mem_lt_sum hb
    exact
      Nat.ModEq.eq_of_lt_of_lt
        ((ZMod.natCast_eq_natCast_iff a b m).mp hab) ha_lt hb_lt

theorem packetPhase_preimage_packetPrefixPhaseSet_card
    {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) {packet : List Nat} (hsum : packet.sum = m)
    (r : Fin packet.length) :
    ((Finset.univ : Finset (ZMod N × ZMod m)).filter
      (fun y => packetPhase hdiv y ∈ packetPrefixPhaseSet m packet r)).card =
        packet.get r * N := by
  rw [packetPhase_preimage_card hdiv,
    packetPrefixPhaseSet_card hsum]

def packetPhaseCoordEquiv {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) :
    ZMod N × ZMod m ≃ ZMod m × ZMod N where
  toFun y := (packetPhase hdiv y, y.1)
  invFun p := (p.2, p.1 - ZMod.castHom hdiv (ZMod m) p.2)
  left_inv y := by
    rcases y with ⟨x, z⟩
    apply Prod.ext
    · rfl
    · dsimp [packetPhase]
      abel_nf
  right_inv p := by
    rcases p with ⟨φ, x⟩
    apply Prod.ext
    · dsimp [packetPhase]
      abel_nf
    · rfl

def packetPhaseIntervalOrdinary {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (packet : List Nat)
    (r : Fin packet.length) (y : ZMod N × ZMod m) : Bool :=
  decide (packetPhase hdiv y ∈ packetPrefixPhaseSet m packet r)

theorem packetPhaseIntervalOrdinary_card
    {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) {packet : List Nat} (hsum : packet.sum = m)
    (r : Fin packet.length) :
    ((Finset.univ : Finset (ZMod N × ZMod m)).filter
      (fun y => packetPhaseIntervalOrdinary hdiv packet r y = true)).card =
        packet.get r * N := by
  convert packetPhase_preimage_packetPrefixPhaseSet_card
    hdiv hsum r using 2
  ext y
  simp [packetPhaseIntervalOrdinary]

theorem packetPhaseIntervalOrdinary_existsUnique
    {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) {packet : List Nat}
    (hsum : packet.sum = m)
    (hpos : ∀ a, a ∈ packet → 0 < a)
    (y : ZMod N × ZMod m) :
    ∃! r : Fin packet.length,
      packetPhaseIntervalOrdinary hdiv packet r y = true := by
  rcases packetPrefixPhaseSet_existsUnique hsum hpos (packetPhase hdiv y) with
    ⟨r, hr, huniq⟩
  refine ⟨r, ?_, ?_⟩
  · simpa [packetPhaseIntervalOrdinary] using hr
  · intro s hs
    apply huniq
    simpa [packetPhaseIntervalOrdinary] using hs

def packetPhaseIntervalStep {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (packet : List Nat) (r : Fin packet.length) :
    ZMod N × ZMod m → ZMod N × ZMod m :=
  fun y =>
    if packetPhaseIntervalOrdinary hdiv packet r y then
      (y.1 + 1, y.2)
    else
      (y.1, y.2 + 1)

def packetPhaseSkewStep {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) : ZMod m × ZMod N → ZMod m × ZMod N :=
  fun p => (p.1 + 1, if p.1 ∈ S then p.2 + 1 else p.2)

def packetPhaseSkewStepInv {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) : ZMod m × ZMod N → ZMod m × ZMod N :=
  fun p =>
    let φ := p.1 - 1
    (φ, if φ ∈ S then p.2 - 1 else p.2)

theorem packetPhaseSkewStep_leftInverse
    {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) :
    Function.LeftInverse
      (packetPhaseSkewStepInv (N := N) (m := m) S)
      (packetPhaseSkewStep (N := N) (m := m) S) := by
  intro p
  rcases p with ⟨φ, x⟩
  by_cases hφ : φ ∈ S
  · ext <;> simp [packetPhaseSkewStep, packetPhaseSkewStepInv, hφ]
  · ext <;> simp [packetPhaseSkewStep, packetPhaseSkewStepInv, hφ]

theorem packetPhaseSkewStep_rightInverse
    {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) :
    Function.RightInverse
      (packetPhaseSkewStepInv (N := N) (m := m) S)
      (packetPhaseSkewStep (N := N) (m := m) S) := by
  intro p
  rcases p with ⟨φ, x⟩
  by_cases hφ : φ - 1 ∈ S
  · ext <;> simp [packetPhaseSkewStep, packetPhaseSkewStepInv, hφ]
  · ext <;> simp [packetPhaseSkewStep, packetPhaseSkewStepInv, hφ]

theorem packetPhaseSkewStep_bijective
    {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) :
    Function.Bijective (packetPhaseSkewStep (N := N) S) :=
  ⟨(packetPhaseSkewStep_leftInverse (N := N) (m := m) S).injective,
    (packetPhaseSkewStep_rightInverse (N := N) (m := m) S).surjective⟩

theorem packetPhaseSkewStep_fst_iterate
    {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod N,
      ((packetPhaseSkewStep S)^[n] p).1 = p.1 + (n : ZMod m)
  | 0, p => by simp
  | n + 1, p => by
      rw [Function.iterate_succ_apply]
      calc
        ((packetPhaseSkewStep S)^[n]
            (packetPhaseSkewStep S p)).1 =
          (packetPhaseSkewStep S p).1 + (n : ZMod m) :=
            packetPhaseSkewStep_fst_iterate S n (packetPhaseSkewStep S p)
        _ = (p.1 + 1) + (n : ZMod m) := rfl
        _ = p.1 + ((n + 1 : Nat) : ZMod m) := by
            simp [Nat.cast_add, Nat.cast_one]
            abel

theorem packetPhaseSkewStep_snd_iterate
    {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) :
    ∀ n : Nat, ∀ p : ZMod m × ZMod N,
      ((packetPhaseSkewStep S)^[n] p).2 =
        p.2 + Finset.sum (Finset.range n)
          (fun k =>
            if p.1 + (k : ZMod m) ∈ S then (1 : ZMod N) else 0)
  | 0, p => by simp
  | n + 1, p => by
      rw [Function.iterate_succ_apply']
      have ih := packetPhaseSkewStep_snd_iterate S n p
      have hfst := packetPhaseSkewStep_fst_iterate S n p
      by_cases hmem : p.1 + (n : ZMod m) ∈ S
      · have hmem' : ((packetPhaseSkewStep S)^[n] p).1 ∈ S := by
          simpa [hfst] using hmem
        have hsum :
            (∑ k ∈ Finset.range (n + 1),
                if p.1 + (k : ZMod m) ∈ S then (1 : ZMod N) else 0) =
              (∑ k ∈ Finset.range n,
                if p.1 + (k : ZMod m) ∈ S then (1 : ZMod N) else 0) + 1 := by
          rw [Finset.sum_range_succ]
          simp [hmem]
        simp [packetPhaseSkewStep, hmem', ih, hsum, add_assoc]
      · have hmem' : ((packetPhaseSkewStep S)^[n] p).1 ∉ S := by
          simpa [hfst] using hmem
        have hsum :
            (∑ k ∈ Finset.range (n + 1),
                if p.1 + (k : ZMod m) ∈ S then (1 : ZMod N) else 0) =
              (∑ k ∈ Finset.range n,
                if p.1 + (k : ZMod m) ∈ S then (1 : ZMod N) else 0) := by
          rw [Finset.sum_range_succ]
          simp [hmem]
        simp [packetPhaseSkewStep, hmem', ih, hsum]

theorem packetPhaseSkewStep_zero_phase_cover
    {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) :
    ∀ p : ZMod m × ZMod N, ∃ x : ZMod N, ∃ k : Nat,
      k < m ∧ (packetPhaseSkewStep S)^[k] (0, x) = p := by
  intro p
  let hitSum : ZMod N :=
    Finset.sum (Finset.range p.1.val)
      (fun k =>
        if (0 : ZMod m) + (k : ZMod m) ∈ S then (1 : ZMod N) else 0)
  refine ⟨p.2 - hitSum, p.1.val, ZMod.val_lt p.1, ?_⟩
  apply Prod.ext
  · rw [packetPhaseSkewStep_fst_iterate]
    simp
  · rw [packetPhaseSkewStep_snd_iterate]
    simp [hitSum]

theorem packetPhaseSkewStep_singleCycle_of_return
    {N m : Nat} [NeZero N] [NeZero m]
    (S : Finset (ZMod m)) (R : ZMod N → ZMod N)
    (hreturn :
      ∀ x : ZMod N, (packetPhaseSkewStep S)^[m] (0, x) = (0, R x))
    (hR : Shared.IsSingleCycleMap R) :
    Shared.IsSingleCycleMap (packetPhaseSkewStep (N := N) S) := by
  refine
    Shared.single_cycle_of_periodic_return_cover
      (packetPhaseSkewStep (N := N) S)
      (fun x : ZMod N => ((0 : ZMod m), x))
      R m
      (packetPhaseSkewStep_bijective (N := N) (m := m) S)
      hreturn
      hR
      ?_
  intro p
  rcases packetPhaseSkewStep_zero_phase_cover (N := N) (m := m) S p with
    ⟨x, k, hk, hp⟩
  exact ⟨x, k, hk, hp⟩

theorem packetPhaseIntervalStep_conj_skew
    {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (packet : List Nat) (r : Fin packet.length)
    (p : ZMod m × ZMod N) :
    packetPhaseCoordEquiv hdiv
      (packetPhaseIntervalStep hdiv packet r
        ((packetPhaseCoordEquiv hdiv).symm p)) =
      packetPhaseSkewStep (packetPrefixPhaseSet m packet r) p := by
  rcases p with ⟨φ, x⟩
  let y : ZMod N × ZMod m :=
    (x, φ - ZMod.castHom hdiv (ZMod m) x)
  have hphase : packetPhase hdiv y = φ := by
    dsimp [y, packetPhase]
    abel
  have hcast : ZMod.castHom hdiv (ZMod m) x = (x.cast : ZMod m) := by
    rw [ZMod.castHom_apply]
  have hphaseCast :
      packetPhase hdiv (x, φ - (x.cast : ZMod m)) = φ := by
    simpa [y, hcast] using hphase
  by_cases hφ : φ ∈ packetPrefixPhaseSet m packet r
  · have hord :
        packetPhaseIntervalOrdinary hdiv packet r y = true := by
      simp [packetPhaseIntervalOrdinary, hphase, hφ]
    have hordCast :
        packetPhaseIntervalOrdinary hdiv packet r
          (x, φ - (x.cast : ZMod m)) = true := by
      simpa [y, hcast] using hord
    apply Prod.ext
    · dsimp [packetPhaseCoordEquiv, packetPhaseIntervalStep,
        packetPhaseSkewStep]
      rw [hordCast]
      simp
      simpa [hphaseCast] using
        packetPhase_step_first hdiv (x, φ - (x.cast : ZMod m))
    · dsimp [packetPhaseCoordEquiv, packetPhaseIntervalStep,
        packetPhaseSkewStep]
      rw [hordCast]
      simp [hφ]
  · have hord :
        packetPhaseIntervalOrdinary hdiv packet r y = false := by
      simp [packetPhaseIntervalOrdinary, hphase, hφ]
    have hordCast :
        packetPhaseIntervalOrdinary hdiv packet r
          (x, φ - (x.cast : ZMod m)) = false := by
      simpa [y, hcast] using hord
    apply Prod.ext
    · dsimp [packetPhaseCoordEquiv, packetPhaseIntervalStep,
        packetPhaseSkewStep]
      rw [hordCast]
      simp
      simpa [hphaseCast] using
        packetPhase_step_second hdiv (x, φ - (x.cast : ZMod m))
    · dsimp [packetPhaseCoordEquiv, packetPhaseIntervalStep,
        packetPhaseSkewStep]
      rw [hordCast]
      simp [hφ]

theorem packetPhaseIntervalStep_singleCycle_of_skew
    {N m : Nat} [NeZero N] [NeZero m]
    (hdiv : m ∣ N) (packet : List Nat) (r : Fin packet.length)
    (hSkew :
      Shared.IsSingleCycleMap
        (packetPhaseSkewStep (N := N)
          (packetPrefixPhaseSet m packet r))) :
    Shared.IsSingleCycleMap
      (packetPhaseIntervalStep hdiv packet r) := by
  refine
    Shared.single_cycle_of_equiv_conj
      (packetPhaseCoordEquiv hdiv).symm
      (packetPhaseIntervalStep hdiv packet r)
      (packetPhaseSkewStep (N := N)
        (packetPrefixPhaseSet m packet r))
      hSkew
      ?_
  intro p
  exact packetPhaseIntervalStep_conj_skew hdiv packet r p

/--
The remaining local packet theorem needed by the active-block cylinder.

This is intentionally isolated from the global torus geometry: unit packet
entries and unit proper prefix sums should produce a phase splitter on every
cycle length `N` divisible by `m`.  This divisibility is necessary for the
packet counts to close around the `ZMod m` coordinate, and the successor
cylinder only applies the theorem with `N = m ^ b`.
-/
def PacketPhaseSplitGoal : Prop :=
  ∀ {N m : Nat} [NeZero N] [NeZero m] {packet : List Nat},
    m ∣ N →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (∀ q : Nat, 0 < q → q < packet.length →
      Nat.Coprime (packet.take q).sum m) →
    Nonempty (PacketPhaseSplit N m packet)

theorem mixedExpansionData_of_mixedLowerWitnessData
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (W : MixedLowerWitnessData Cyl) :
    MixedExpansionData Cyl where
  mixed_lower := by
    intro U hUne hUuniv
    let E := W.witness U hUne hUuniv
    have hsubset :
        E ⊆
          ((Finset.univ : Finset (Shared.TorusVertex (b + 1) m)).filter
            (fun x =>
              0 < (Cyl.incidence.active x ∩ U).card ∧
                (Cyl.incidence.active x ∩ U).card < T)) := by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ x, W.witness_mixed U hUne hUuniv x hx⟩
    have hcard :
        E.card ≤
          ((Finset.univ : Finset (Shared.TorusVertex (b + 1) m)).filter
            (fun x =>
              0 < (Cyl.incidence.active x ∩ U).card ∧
                (Cyl.incidence.active x ∩ U).card < T)).card :=
      Finset.card_le_card hsubset
    rw [W.witness_card U hUne hUuniv] at hcard
    rw [Cyl.incidence.mixedCount_eq_card_filter U]
    exact hcard

namespace MixedExpansionData

theorem mixed_lower_compl
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) {U : Finset (Fin (b + T))}
    (hUne : U.Nonempty) (hUuniv : U ≠ Finset.univ) :
    m ^ b ≤ (Cyl.incidence).mixedCount Uᶜ := by
  classical
  have hcomp_ne : Uᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    exact hUuniv ((Finset.compl_eq_empty_iff U).mp hEmpty)
  have hcomp_univ : Uᶜ ≠ (Finset.univ : Finset (Fin (b + T))) := by
    intro hUniv
    exact hUne.ne_empty ((Finset.compl_eq_univ_iff U).mp hUniv)
  exact D.mixed_lower Uᶜ hcomp_ne hcomp_univ

theorem slack_error_le_mixedCount_mul_proper_min
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) {U : Finset (Fin (b + T))}
    (hUne : U.Nonempty) (hUuniv : U ≠ Finset.univ)
    (hTpos : 0 < T) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card)
      ≤ (Cyl.incidence).mixedCount U * min S.card (T - S.card) := by
  have hbaseScale : m * (b + T) ≤ m * (b + T) * T := by
    exact Nat.le_mul_of_pos_right (m * (b + T)) hTpos
  have hbaseLtPow : m * (b + T) < m ^ b :=
    hbaseScale.trans_lt hSlack
  have hbaseLeMixed : m * (b + T) ≤ (Cyl.incidence).mixedCount U :=
    Nat.le_of_lt (hbaseLtPow.trans_le (D.mixed_lower U hUne hUuniv))
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_right (min S.card (T - S.card)) hbaseLeMixed

theorem slack_error_le_mixedCount_compl_mul_proper_min
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) {U : Finset (Fin (b + T))}
    (hUne : U.Nonempty) (hUuniv : U ≠ Finset.univ)
    (hTpos : 0 < T) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card)
      ≤ (Cyl.incidence).mixedCount Uᶜ * min S.card (T - S.card) := by
  have hbaseScale : m * (b + T) ≤ m * (b + T) * T := by
    exact Nat.le_mul_of_pos_right (m * (b + T)) hTpos
  have hbaseLtPow : m * (b + T) < m ^ b :=
    hbaseScale.trans_lt hSlack
  have hbaseLeMixed : m * (b + T) ≤ (Cyl.incidence).mixedCount Uᶜ :=
    Nat.le_of_lt (hbaseLtPow.trans_le (D.mixed_lower_compl hUne hUuniv))
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_right (min S.card (T - S.card)) hbaseLeMixed

theorem hallCuts_of_scaled_error_le_slack
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) (hTpos : 0 < T)
    (hSlack : m ^ b > m * (b + T) * T)
    (M : ActiveHall.CountMatrix Cyl.incidence)
    (hScaled :
      ∀ U : Finset (Fin (b + T)), ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ Finset.univ →
        S.Nonempty → S ≠ Finset.univ →
          T * M.cutMass U S ≤
            S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c) +
              m * (b + T) * min S.card (T - S.card)) :
    M.HallCuts := by
  apply M.hallCuts_of_nontrivial_scaled_bary_error_le_mixed hTpos
  intro U S hUne hUuniv hSne hSuniv
  exact
    (hScaled U S hUne hUuniv hSne hSuniv).trans
      (Nat.add_le_add_left
        (D.slack_error_le_mixedCount_mul_proper_min
          hUne hUuniv hTpos hSlack S)
        (S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c)))

theorem feasibleWithResidues_of_scaled_error_le_slack
    {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : MixedExpansionData Cyl) (hTpos : 0 < T)
    (hSlack : m ^ b > m * (b + T) * T)
    {R : ActiveHall.ResidueSpec m T (Fin (b + T))}
    (M : ActiveHall.CountMatrix Cyl.incidence)
    (hResidues : M.HasResidues R)
    (hScaled :
      ∀ U : Finset (Fin (b + T)), ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ Finset.univ →
        S.Nonempty → S ≠ Finset.univ →
          T * M.cutMass U S ≤
            S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c) +
              m * (b + T) * min S.card (T - S.card)) :
    ActiveHall.FeasibleWithResidues Cyl.incidence R :=
  ⟨M, D.hallCuts_of_scaled_error_le_slack hTpos hSlack M hScaled,
    hResidues⟩

end MixedExpansionData

theorem incidence_colorDegree_le_mixedCount_of_mem_of_card_lt
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : ActiveHall.Incidence T X C) {U : Finset C} {c : C}
    (hc : c ∈ U) (hcard : U.card < T) :
    I.colorDegree c ≤ I.mixedCount U := by
  classical
  rw [ActiveHall.Incidence.colorDegree, I.mixedCount_eq_card_filter U]
  apply Finset.card_le_card
  intro x hx
  have hcx : c ∈ I.active x := (Finset.mem_filter.mp hx).2
  have hhit : (I.active x ∩ U).Nonempty :=
    ⟨c, Finset.mem_inter.mpr ⟨hcx, hc⟩⟩
  have hlt : (I.active x ∩ U).card < T := by
    have hsub : I.active x ∩ U ⊆ U := by
      intro d hd
      exact (Finset.mem_inter.mp hd).2
    exact (Finset.card_le_card hsub).trans_lt hcard
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ x, hhit.card_pos, hlt⟩

namespace ActiveBlockData

theorem active_complement_pos {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    0 < m - (D.activeBlock c) := by
  exact Nat.sub_pos_of_lt (D.activeBlock_lt c)

theorem activeBlock_isUnit {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    IsUnit ((D.activeBlock c : Nat) : ZMod m) :=
  (ZMod.isUnit_iff_coprime (D.activeBlock c) m).2
    (D.activeBlock_coprime c)

theorem active_complement_coprime {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    Nat.Coprime (m - (D.activeBlock c)) m :=
  (Nat.coprime_self_sub_left (Nat.le_of_lt (D.activeBlock_lt c))).2
    (D.activeBlock_coprime c)

theorem active_complement_isUnit {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    IsUnit (((m - (D.activeBlock c)) : Nat) : ZMod m) :=
  (ZMod.isUnit_iff_coprime (m - (D.activeBlock c)) m).2
    (D.active_complement_coprime c)

theorem active_degree_mod {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (hb : 0 < b) (c : Fin (b + T)) :
    (((Cyl.incidence).colorDegree c : Nat) : ZMod m) = 0 := by
  rw [D.active_degree_eq c]
  exact ActiveHall.zmod_natCast_mul_pow_eq_zero_of_pos hb

theorem active_degree_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    m ^ b ≤ (Cyl.incidence).colorDegree c := by
  rw [D.active_degree_eq c]
  have hfactor : 1 ≤ m - (D.activeBlock c) := by
    exact D.active_complement_pos c
  simpa using Nat.mul_le_mul_right (m ^ b) hfactor

theorem mixed_lower_of_card_lt {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hUne : U.Nonempty) (hcard : U.card < T) :
    m ^ b ≤ (Cyl.incidence).mixedCount U := by
  rcases hUne with ⟨c, hc⟩
  exact (D.active_degree_lower_bound c).trans
    (incidence_colorDegree_le_mixedCount_of_mem_of_card_lt
      Cyl.incidence hc hcard)

theorem mixedExpansionData_of_successor {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (hT : T = b + 1) :
    MixedExpansionData Cyl := by
  classical
  refine ⟨?_⟩
  intro U hUne hUuniv
  by_cases hcard : U.card < T
  · exact D.mixed_lower_of_card_lt hUne hcard
  · have hcomp_ne : Uᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      exact hUuniv ((Finset.compl_eq_empty_iff U).mp hEmpty)
    have hcard_ge : T ≤ U.card := Nat.le_of_not_gt hcard
    have htotal :
        U.card + Uᶜ.card = b + T := by
      simpa using
        (Finset.card_add_card_compl U :
          U.card + Uᶜ.card = Fintype.card (Fin (b + T)))
    have hcomp_card : Uᶜ.card < T := by
      omega
    have hmix := D.mixed_lower_of_card_lt hcomp_ne hcomp_card
    rw [Cyl.incidence.mixedCount_compl U] at hmix
    exact hmix

theorem active_degree_upper_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    (Cyl.incidence).colorDegree c ≤ (m - 1) * m ^ b := by
  rw [D.active_degree_eq c]
  have hfactor : m - (D.activeBlock c) ≤ m - 1 := by
    have hpos := D.activeBlock_pos c
    omega
  exact Nat.mul_le_mul_right (m ^ b) hfactor

theorem active_degree_pos {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (c : Fin (b + T)) :
    0 < (Cyl.incidence).colorDegree c := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hpow : 0 < m ^ b := pow_pos hmpos b
  exact lt_of_lt_of_le hpow (D.active_degree_lower_bound c)

theorem active_degree_dvd_modulus {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (hb : 0 < b) (c : Fin (b + T)) :
    m ∣ (Cyl.incidence).colorDegree c :=
  (ZMod.natCast_eq_zero_iff ((Cyl.incidence).colorDegree c) m).mp
    (D.active_degree_mod hb c)

theorem modulus_le_active_degree {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (hb : 0 < b) (c : Fin (b + T)) :
    m ≤ (Cyl.incidence).colorDegree c :=
  Nat.le_of_dvd (D.active_degree_pos c)
    (D.active_degree_dvd_modulus hb c)

theorem sum_colorDegree_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) (U : Finset (Fin (b + T))) :
    U.card * m ^ b ≤
      ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hsum :
      (∑ c ∈ U, m ^ b) ≤
        ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
    exact Finset.sum_le_sum (fun c _hc => D.active_degree_lower_bound c)
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

theorem sum_colorDegree_nonempty_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) :
    m ^ b ≤ ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hcard : 1 ≤ U.card := hU.card_pos
  have hmul : m ^ b ≤ U.card * m ^ b := by
    simpa using Nat.mul_le_mul_right (m ^ b) hcard
  exact hmul.trans (D.sum_colorDegree_lower_bound U)

theorem sum_colorDegree_compl_lower_bound {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) :
    m ^ b ≤
      ∑ c ∈ Uᶜ, (Cyl.incidence).colorDegree c := by
  classical
  have hcomp : Uᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    exact hU ((Finset.compl_eq_empty_iff U).mp hEmpty)
  exact D.sum_colorDegree_nonempty_lower_bound hcomp

theorem slack_error_lt_sum_colorDegree_nonempty {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hscale : m * (b + T) * k ≤ m * (b + T) * T := by
    exact Nat.mul_le_mul_left (m * (b + T)) hk
  have hlt_pow : m * (b + T) * k < m ^ b :=
    lt_of_le_of_lt hscale hSlack
  exact hlt_pow.trans_le (D.sum_colorDegree_nonempty_lower_bound hU)

theorem slack_error_lt_sum_colorDegree_compl {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      ∑ c ∈ Uᶜ, (Cyl.incidence).colorDegree c := by
  have hscale : m * (b + T) * k ≤ m * (b + T) * T := by
    exact Nat.mul_le_mul_left (m * (b + T)) hk
  have hlt_pow : m * (b + T) * k < m ^ b :=
    lt_of_le_of_lt hscale hSlack
  exact hlt_pow.trans_le (D.sum_colorDegree_compl_lower_bound hU)

theorem slack_error_lt_sum_colorDegree_nonempty_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      ∑ c ∈ U, (Cyl.incidence).colorDegree c := by
  have hcard : S.card ≤ T := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hmin : min S.card (T - S.card) ≤ T :=
    (Nat.min_le_left S.card (T - S.card)).trans hcard
  exact D.slack_error_lt_sum_colorDegree_nonempty hU hSlack
    hmin

theorem slack_error_lt_sum_colorDegree_compl_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      ∑ c ∈ Uᶜ, (Cyl.incidence).colorDegree c := by
  have hcard : S.card ≤ T := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hmin : min S.card (T - S.card) ≤ T :=
    (Nat.min_le_left S.card (T - S.card)).trans hcard
  exact D.slack_error_lt_sum_colorDegree_compl hU hSlack
    hmin

theorem sum_colorDegree_le_T_mul_hitCount {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (_D : ActiveBlockData Cyl) (U : Finset (Fin (b + T))) :
    (∑ c ∈ U, (Cyl.incidence).colorDegree c) ≤
      T * (Cyl.incidence).hitCount U :=
  ActiveHall.Incidence.sum_colorDegree_on_le_hitCount_mul
    Cyl.incidence U

theorem slack_error_lt_T_mul_hitCount_nonempty {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      T * (Cyl.incidence).hitCount U :=
  (D.slack_error_lt_sum_colorDegree_nonempty hU hSlack hk).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount U)

theorem slack_error_lt_T_mul_hitCount_compl {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    {k : Nat} (hk : k ≤ T) :
    m * (b + T) * k <
      T * (Cyl.incidence).hitCount Uᶜ :=
  (D.slack_error_lt_sum_colorDegree_compl hU hSlack hk).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount Uᶜ)

theorem slack_error_lt_T_mul_hitCount_nonempty_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U.Nonempty) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      T * (Cyl.incidence).hitCount U :=
  (D.slack_error_lt_sum_colorDegree_nonempty_min hU hSlack S).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount U)

theorem slack_error_lt_T_mul_hitCount_compl_min {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) {U : Finset (Fin (b + T))}
    (hU : U ≠ Finset.univ) (hSlack : m ^ b > m * (b + T) * T)
    (S : Finset (Fin T)) :
    m * (b + T) * min S.card (T - S.card) <
      T * (Cyl.incidence).hitCount Uᶜ :=
  (D.slack_error_lt_sum_colorDegree_compl_min hU hSlack S).trans_le
    (D.sum_colorDegree_le_T_mul_hitCount Uᶜ)

theorem sum_active_complement_eq {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) :
    (∑ c : Fin (b + T), (m - D.activeBlock c)) = T * m := by
  classical
  have hdegSum := ActiveHall.Incidence.sum_colorDegree Cyl.incidence
  have hleft :
      (∑ c : Fin (b + T), (Cyl.incidence).colorDegree c)
        =
      (∑ c : Fin (b + T), (m - D.activeBlock c)) * m ^ b := by
    calc
      (∑ c : Fin (b + T), (Cyl.incidence).colorDegree c)
          = ∑ c : Fin (b + T), (m - D.activeBlock c) * m ^ b := by
              apply Finset.sum_congr rfl
              intro c _hc
              exact D.active_degree_eq c
      _ = (∑ c : Fin (b + T), (m - D.activeBlock c)) * m ^ b := by
              rw [Finset.sum_mul]
  have hright :
      T * Fintype.card (Shared.TorusVertex (b + 1) m) =
        (T * m) * m ^ b := by
    rw [Shared.card_torusVertex, pow_succ]
    ring
  have hmul :
      (∑ c : Fin (b + T), (m - D.activeBlock c)) * m ^ b =
        (T * m) * m ^ b := by
    rw [← hleft, hdegSum, hright]
  exact Nat.mul_right_cancel
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) b) hmul

theorem sum_activeBlock_eq {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (D : ActiveBlockData Cyl) :
    (∑ c : Fin (b + T), D.activeBlock c) = b * m := by
  classical
  have hcomp := D.sum_active_complement_eq
  have hsum_add :
      (∑ c : Fin (b + T), D.activeBlock c) +
          (∑ c : Fin (b + T), (m - D.activeBlock c))
        =
      (b + T) * m := by
    calc
      (∑ c : Fin (b + T), D.activeBlock c) +
          (∑ c : Fin (b + T), (m - D.activeBlock c))
          = ∑ c : Fin (b + T), (D.activeBlock c + (m - D.activeBlock c)) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ _c : Fin (b + T), m := by
              apply Finset.sum_congr rfl
              intro c _hc
              exact Nat.add_sub_of_le (Nat.le_of_lt (D.activeBlock_lt c))
      _ = (b + T) * m := by
              simp [Finset.sum_const, Fintype.card_fin]
  rw [hcomp] at hsum_add
  have htarget : (b + T) * m = b * m + T * m := by
    ring
  rw [htarget] at hsum_add
  exact Nat.add_right_cancel hsum_add

theorem isCylinder_of_activeBlockData {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (ordinary_unique :
      ∀ x : Shared.TorusVertex (b + 1) m,
        ∀ i : Fin (b + 1), i ≠ activeDir b →
          ∃! c : Fin (b + T), Cyl.dir c x = i)
    (color_hamiltonian :
      ∀ c : Fin (b + T), Shared.IsSingleCycleMap (Cyl.step c))
    (D : ActiveBlockData Cyl) (hb : 0 < b) :
    IsCylinder Cyl where
  ordinary_unique := ordinary_unique
  color_hamiltonian := color_hamiltonian
  active_degree_mod := D.active_degree_mod hb

end ActiveBlockData

namespace Cylinder

theorem active_fiber_card {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (x : Shared.TorusVertex (b + 1) m) :
    ((Finset.univ : Finset (Fin (b + T))).filter
      (fun c => Cyl.dir c x = activeDir b)).card = T :=
  Cyl.active_card x

theorem active_direction_exists_of_pos {b m T : Nat}
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (x : Shared.TorusVertex (b + 1) m) (hT : 0 < T) :
    ∃ c : Fin (b + T), Cyl.dir c x = activeDir b := by
  classical
  have hcard := Cyl.active_fiber_card x
  have hpos :
      0 < ((Finset.univ : Finset (Fin (b + T))).filter
        (fun c => Cyl.dir c x = activeDir b)).card := by
    omega
  rcases Finset.card_pos.mp hpos with ⟨c, hc⟩
  exact ⟨c, (Finset.mem_filter.mp hc).2⟩

end Cylinder

namespace IsCylinder

theorem ordinary_direction_exists {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl)
    (x : Shared.TorusVertex (b + 1) m)
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    ∃ c : Fin (b + T), Cyl.dir c x = i := by
  rcases hCyl.ordinary_unique x i hi with ⟨c, hc, _huniq⟩
  exact ⟨c, hc⟩

theorem ordinary_fiber_card {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl)
    (x : Shared.TorusVertex (b + 1) m)
    (i : Fin (b + 1)) (hi : i ≠ activeDir b) :
    ((Finset.univ : Finset (Fin (b + T))).filter
      (fun c => Cyl.dir c x = i)).card = 1 := by
  classical
  rcases hCyl.ordinary_unique x i hi with ⟨c, hc, huniq⟩
  rw [Finset.card_eq_one]
  refine ⟨c, ?_⟩
  ext d
  constructor
  · intro hd
    rw [Finset.mem_filter] at hd
    simp [huniq d hd.2]
  · intro hd
    have hdc : d = c := by
      simpa using hd
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ d, ?_⟩
    rw [hdc]
    exact hc

theorem dir_fiber_card {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl)
    (x : Shared.TorusVertex (b + 1) m)
    (i : Fin (b + 1)) :
    ((Finset.univ : Finset (Fin (b + T))).filter
      (fun c => Cyl.dir c x = i)).card =
        if i = activeDir b then T else 1 := by
  by_cases hi : i = activeDir b
  · subst i
    simp [Cylinder.active_fiber_card]
  · simp [hi, hCyl.ordinary_fiber_card x i hi]

end IsCylinder

namespace Cylinder

theorem step_activeDir_eq_of_dir_ne {b m T : Nat} {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (c : Fin (b + T)) (x : Shared.TorusVertex (b + 1) m)
    (hdir : Cyl.dir c x ≠ activeDir b) :
    (Cyl.step c x) (activeDir b) = x (activeDir b) := by
  simp [Cylinder.step, Shared.torusBasis, hdir.symm]

theorem dir_ne_activeDir_of_colorDegree_zero {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    {c : Fin (b + T)}
    (hdeg : (Cyl.incidence).colorDegree c = 0)
    (x : Shared.TorusVertex (b + 1) m) :
    Cyl.dir c x ≠ activeDir b := by
  classical
  have hfilter_empty :
      ((Finset.univ : Finset (Shared.TorusVertex (b + 1) m)).filter
        (fun x => c ∈ (Cyl.incidence).active x)) = ∅ := by
    exact Finset.card_eq_zero.mp hdeg
  have hnot : c ∉ (Cyl.incidence).active x := by
    intro hc
    have hx :
        x ∈ ((Finset.univ : Finset (Shared.TorusVertex (b + 1) m)).filter
          (fun x => c ∈ (Cyl.incidence).active x)) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hc⟩
    rw [hfilter_empty] at hx
    simp at hx
  intro hdir
  exact hnot (by
    simp [Cylinder.incidence, Cylinder.active, hdir])

theorem iterate_step_activeDir_eq_of_colorDegree_zero
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    {c : Fin (b + T)}
    (hdeg : (Cyl.incidence).colorDegree c = 0) :
    ∀ n : Nat, ∀ x : Shared.TorusVertex (b + 1) m,
      ((Cyl.step c)^[n] x) (activeDir b) = x (activeDir b)
  | 0, x => by simp
  | n + 1, x => by
      rw [Function.iterate_succ_apply']
      calc
        (Cyl.step c ((Cyl.step c)^[n] x)) (activeDir b)
            = ((Cyl.step c)^[n] x) (activeDir b) := by
                exact Cyl.step_activeDir_eq_of_dir_ne c ((Cyl.step c)^[n] x)
                  (Cyl.dir_ne_activeDir_of_colorDegree_zero hdeg
                    ((Cyl.step c)^[n] x))
        _ = x (activeDir b) :=
                Cyl.iterate_step_activeDir_eq_of_colorDegree_zero hdeg n x

end Cylinder

namespace IsCylinder

theorem active_degree_pos {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (hm : 1 < m) (c : Fin (b + T)) :
    0 < (Cyl.incidence).colorDegree c := by
  classical
  by_contra hpos
  have hdeg : (Cyl.incidence).colorDegree c = 0 :=
    Nat.eq_zero_of_not_pos hpos
  let x0 : Shared.TorusVertex (b + 1) m := 0
  let y : Shared.TorusVertex (b + 1) m :=
    Shared.torusBasis (b + 1) m (activeDir b)
  rcases (hCyl.color_hamiltonian c).2 x0 y with ⟨n, hn⟩
  have hcoord := congrArg (fun x : Shared.TorusVertex (b + 1) m =>
    x (activeDir b)) hn
  have hiter :=
    Cyl.iterate_step_activeDir_eq_of_colorDegree_zero hdeg n x0
  have h01 : (0 : ZMod m) = 1 := by
    simpa [x0, y, Shared.torusBasis] using hiter.symm.trans hcoord
  have h10 : (1 : ZMod m) ≠ 0 := by
    intro h
    have h' : ((1 : Nat) : ZMod m) = 0 := by simpa using h
    have hdvd : m ∣ 1 := (ZMod.natCast_eq_zero_iff 1 m).mp h'
    have hmle : m ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hdvd
    omega
  exact h10 h01.symm

theorem active_degree_dvd_modulus {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (c : Fin (b + T)) :
    m ∣ (Cyl.incidence).colorDegree c := by
  exact (ZMod.natCast_eq_zero_iff ((Cyl.incidence).colorDegree c) m).mp
    (hCyl.active_degree_mod c)

theorem modulus_le_active_degree {b m T : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m T packets}
    (hCyl : IsCylinder Cyl) (hm : 1 < m) (c : Fin (b + T)) :
    m ≤ (Cyl.incidence).colorDegree c := by
  exact Nat.le_of_dvd (hCyl.active_degree_pos hm c)
    (hCyl.active_degree_dvd_modulus c)

end IsCylinder

structure ActiveSymboling {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  R : ActiveHall.ResidueSpec m T (Fin (b + T))
  Φ : ActiveHall.Symboling Cyl.incidence

noncomputable def expandedColorDir
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) (A : ActiveSymboling Cyl) :
    Shared.TorusColor (b + T) →
      Shared.TorusVertex (b + T) m →
      Shared.TorusDirection (b + T) :=
  fun c x =>
    let y := collapseVertex b m T x
    let i := Cyl.dir c y
    if hactive : i = activeDir b then
      tailExpandedDir b
        ((A.Φ.equiv y).symm
          ⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩)
    else
      ordinaryExpandedDir i hactive

theorem expandedColorDir_eq_ordinary_of_inactive
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (c : Fin (b + T)) (x : Shared.TorusVertex (b + T) m)
    (hdir : Cyl.dir c (collapseVertex b m T x) ≠ activeDir b) :
    expandedColorDir Cyl A c x =
      ordinaryExpandedDir (Cyl.dir c (collapseVertex b m T x)) hdir := by
  simp [expandedColorDir, hdir]

theorem expandedColorDir_eq_tail_of_active_symbol
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (c : Fin (b + T)) (x : Shared.TorusVertex (b + T) m)
    (σ : Fin T)
    (hdir : Cyl.dir c (collapseVertex b m T x) = activeDir b)
    (hsym : ∀ hmem : c ∈ Cyl.active (collapseVertex b m T x),
      (A.Φ.equiv (collapseVertex b m T x)).symm ⟨c, hmem⟩ = σ) :
    expandedColorDir Cyl A c x = tailExpandedDir b σ := by
  have hmem : c ∈ Cyl.active (collapseVertex b m T x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hdir⟩
  dsimp [expandedColorDir]
  simp only [hdir, ↓reduceDIte]
  exact congrArg (tailExpandedDir b) (hsym hmem)

theorem activeSymboling_symm_congr
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} (A : ActiveSymboling Cyl)
    {y0 y1 : Shared.TorusVertex (b + 1) m} {c : Fin (b + T)}
    (hy : y0 = y1)
    (h0 : c ∈ Cyl.active y0) (h1 : c ∈ Cyl.active y1) :
    (A.Φ.equiv y0).symm
        (⟨c, by
          change c ∈ Cyl.active y0
          exact h0⟩ :
          {c : Fin (b + T) // c ∈ (Cyl.incidence).active y0}) =
      (A.Φ.equiv y1).symm
        (⟨c, by
          change c ∈ Cyl.active y1
          exact h1⟩ :
          {c : Fin (b + T) // c ∈ (Cyl.incidence).active y1}) := by
  cases hy
  apply congrArg (A.Φ.equiv y0).symm
  apply Subtype.ext
  rfl

theorem collapseVertex_cayleyColorStep_expandedColorDir
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) (A : ActiveSymboling Cyl)
    (c : Fin (b + T)) (x : Shared.TorusVertex (b + T) m) :
    collapseVertex b m T
        (Shared.cayleyColorStep (expandedColorDir Cyl A) c x)
      =
    Cyl.step c (collapseVertex b m T x) := by
  classical
  let y := collapseVertex b m T x
  by_cases hactive : Cyl.dir c y = activeDir b
  · have hdir :
        expandedColorDir Cyl A c x =
          tailExpandedDir b
            ((A.Φ.equiv y).symm
              ⟨c, by
                change c ∈ Cyl.active y
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_univ c, hactive⟩⟩) := by
      simp [expandedColorDir, y, hactive]
    rw [Shared.cayleyColorStep, hdir,
      collapseVertex_add_tailExpandedDir]
    simp [Cylinder.step, y, hactive]
  · have hdir :
        expandedColorDir Cyl A c x =
          ordinaryExpandedDir (Cyl.dir c y) hactive := by
      simp [expandedColorDir, y, hactive]
    rw [Shared.cayleyColorStep, hdir,
      collapseVertex_add_ordinaryExpandedDir]
    simp [Cylinder.step, y]

/--
Fiber-dependent active-tail expansion.

This is the common Latin/collapse skeleton needed by the final active
prefix-count lift.  At an active compressed edge, the symboling gives the
incoming active symbol, and `tailPerm` may permute the active tail symbols as a
function of the collapsed base point and collapse fiber.  Any such permutation
preserves the edge partition and the projection to the compressed cylinder.
-/
noncomputable def activePermutedColorDir
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m (n + 1) packets) (A : ActiveSymboling Cyl)
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1))) :
    Shared.TorusColor (b + (n + 1)) →
      Shared.TorusVertex (b + (n + 1)) m →
      Shared.TorusDirection (b + (n + 1)) :=
  fun c x =>
    let y := collapseVertex b m (n + 1) x
    let z := collapseFiberInit b m n x
    let i := Cyl.dir c y
    if hactive : i = activeDir b then
      tailExpandedDir b
        ((tailPerm y z)
          ((A.Φ.equiv y).symm
            ⟨c, by
              change c ∈ Cyl.active y
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_univ c, hactive⟩⟩))
    else
      ordinaryExpandedDir i hactive

theorem collapseVertex_cayleyColorStep_activePermutedColorDir
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m (n + 1) packets) (A : ActiveSymboling Cyl)
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (c : Fin (b + (n + 1)))
    (x : Shared.TorusVertex (b + (n + 1)) m) :
    collapseVertex b m (n + 1)
        (Shared.cayleyColorStep (activePermutedColorDir Cyl A tailPerm) c x)
      =
    Cyl.step c (collapseVertex b m (n + 1) x) := by
  classical
  let y := collapseVertex b m (n + 1) x
  let z := collapseFiberInit b m n x
  by_cases hactive : Cyl.dir c y = activeDir b
  · have hdir :
        activePermutedColorDir Cyl A tailPerm c x =
          tailExpandedDir b
            ((tailPerm y (collapseFiberInit b m n x))
              ((A.Φ.equiv y).symm
                ⟨c, by
                  change c ∈ Cyl.active y
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_univ c, hactive⟩⟩)) := by
      simp [activePermutedColorDir, y, hactive]
    rw [Shared.cayleyColorStep, hdir,
      collapseVertex_add_tailExpandedDir]
    simp [Cylinder.step, y, hactive]
  · have hdir :
        activePermutedColorDir Cyl A tailPerm c x =
          ordinaryExpandedDir (Cyl.dir c y) hactive := by
      simp [activePermutedColorDir, y, hactive]
    rw [Shared.cayleyColorStep, hdir,
      collapseVertex_add_ordinaryExpandedDir]
    simp [Cylinder.step, y]

theorem activePermutedColorDirEdgePartition
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (hCyl : IsCylinder Cyl) :
    Shared.IsCayleyEdgePartition
      (activePermutedColorDir Cyl A tailPerm) := by
  classical
  intro x j
  let y := collapseVertex b m (n + 1) x
  let z := collapseFiberInit b m n x
  by_cases hj : j.val < b
  · let i : Fin (b + 1) := ordinaryBaseDirOfExpandedDir j hj
    have hi : i ≠ activeDir b :=
      ordinaryBaseDirOfExpandedDir_ne_active j hj
    rcases hCyl.ordinary_unique y i hi with ⟨c, hc, huniq⟩
    refine ⟨c, ?_, ?_⟩
    · have hnot : Cyl.dir c y ≠ activeDir b := by
        rw [hc]
        exact hi
      apply Fin.ext
      have hval' :
          (activePermutedColorDir Cyl A tailPerm c x).val =
            (Cyl.dir c y).val := by
        simp [activePermutedColorDir, y, hnot, ordinaryExpandedDir]
      rw [hval']
      simp [hc, i, ordinaryBaseDirOfExpandedDir]
    · intro d hd
      have hnot : Cyl.dir d y ≠ activeDir b := by
        intro hactive
        have hval := congrArg Fin.val hd
        have hge :
            b ≤ (activePermutedColorDir Cyl A tailPerm d x).val := by
          simp [activePermutedColorDir, y, hactive, tailExpandedDir]
        rw [hval] at hge
        omega
      have hdir : Cyl.dir d y = i := by
        apply Fin.ext
        have hval := congrArg Fin.val hd
        have hval' :
            (activePermutedColorDir Cyl A tailPerm d x).val =
              (Cyl.dir d y).val := by
          simp [activePermutedColorDir, y, hnot, ordinaryExpandedDir]
        rw [hval'] at hval
        simpa [i, ordinaryBaseDirOfExpandedDir] using hval
      exact huniq d hdir
  · have hjge : b ≤ j.val := by omega
    let σ : Fin (n + 1) := tailSymbolOfExpandedDir j hjge
    let ρ : Fin (n + 1) := (tailPerm y z).symm σ
    let p : {c : Fin (b + (n + 1)) //
        c ∈ (Cyl.incidence).active y} :=
      A.Φ.equiv y ρ
    let c : Fin (b + (n + 1)) := p.1
    have hcActive : Cyl.dir c y = activeDir b := by
      have hp : c ∈ Cyl.active y := by
        simp [Cylinder.incidence, c, p]
      exact (Finset.mem_filter.mp hp).2
    have hsub :
        (⟨c, by
          change c ∈ Cyl.active y
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcActive⟩⟩ :
          {c : Fin (b + (n + 1)) // c ∈ (Cyl.incidence).active y}) = p := by
      apply Subtype.ext
      rfl
    have hsymm :
        (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcActive⟩⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}) = ρ := by
      rw [hsub]
      exact (A.Φ.equiv y).symm_apply_apply ρ
    have hperm : (tailPerm y z) ρ = σ := by
      simp [ρ]
    refine ⟨c, ?_, ?_⟩
    · calc
        activePermutedColorDir Cyl A tailPerm c x =
            tailExpandedDir b ((tailPerm y z) ρ) := by
          simp [activePermutedColorDir, y, z, hcActive, hsymm]
        _ = tailExpandedDir b σ := by rw [hperm]
        _ = j := tailExpandedDir_of_tailSymbol j hjge
    · intro d hd
      have hactive : Cyl.dir d y = activeDir b := by
        by_contra hnot
        have hval := congrArg Fin.val hd
        have hlt : (activePermutedColorDir Cyl A tailPerm d x).val < b := by
          simp [activePermutedColorDir, y, hnot, ordinaryExpandedDir_val_lt]
        rw [hval] at hlt
        omega
      have hdmem : d ∈ Cyl.active y :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ d, hactive⟩
      let q : {c : Fin (b + (n + 1)) //
          c ∈ (Cyl.incidence).active y} :=
        ⟨d, by
          change d ∈ Cyl.active y
          exact hdmem⟩
      have hsymm_d :
          (tailPerm y z) ((A.Φ.equiv y).symm q) = σ := by
        apply tailExpandedDir_injective (b := b)
        calc
          tailExpandedDir b ((tailPerm y z) ((A.Φ.equiv y).symm q))
              = activePermutedColorDir Cyl A tailPerm d x := by
                simp [activePermutedColorDir, y, z, hactive, q]
          _ = j := hd
          _ = tailExpandedDir b σ :=
                (tailExpandedDir_of_tailSymbol j hjge).symm
      have hsymm_q : (A.Φ.equiv y).symm q = ρ :=
        (tailPerm y z).injective (by simpa [hperm] using hsymm_d)
      have hq : q = p := by
        have happly := congrArg (A.Φ.equiv y) hsymm_q
        simpa [q, p] using happly
      exact congrArg Subtype.val hq

structure IsActiveSymboling {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (A : ActiveSymboling Cyl) : Prop where
  has_residues : A.Φ.HasResidues A.R

def IsPrimitiveActiveSymboling {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (A : ActiveSymboling Cyl) : Prop :=
  IsActiveSymboling A ∧
    (∀ c : Fin (b + T), IsUnit (A.R.target c ⟨0, by omega⟩)) ∧
    (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit (A.R.target c σ - A.R.target c ⟨1, by omega⟩))

def ActiveSymbolingCountsPrimitive {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (A : ActiveSymboling Cyl) : Prop :=
  (∀ c : Fin (b + T),
    IsUnit (((A.Φ.count c ⟨0, by omega⟩ : Nat) : ZMod m))) ∧
    (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit
        ((((A.Φ.count c σ : Nat) : ZMod m) -
          ((A.Φ.count c ⟨1, by omega⟩ : Nat) : ZMod m))))

theorem activeSymbolingCountsPrimitive_of_isPrimitive
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T) :
    IsPrimitiveActiveSymboling hT A →
      ActiveSymbolingCountsPrimitive hT A := by
  intro hA
  rcases hA with ⟨hValid, hZero, hNumeric⟩
  refine ⟨?_, ?_⟩
  · intro c
    have hres := hValid.has_residues c ⟨0, by omega⟩
    rw [hres]
    exact hZero c
  · intro c σ hσ
    have hresσ := hValid.has_residues c σ
    have hresΔ := hValid.has_residues c ⟨1, by omega⟩
    rw [hresσ, hresΔ]
    exact hNumeric c σ hσ

theorem isPrimitiveActiveSymboling_of_countsPrimitive
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T) :
    IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      IsPrimitiveActiveSymboling hT A := by
  intro hA hPrim
  rcases hPrim with ⟨hZero, hNumeric⟩
  refine ⟨hA, ?_, ?_⟩
  · intro c
    have hres := hA.has_residues c ⟨0, by omega⟩
    rw [← hres]
    exact hZero c
  · intro c σ hσ
    have hresσ := hA.has_residues c σ
    have hresΔ := hA.has_residues c ⟨1, by omega⟩
    rw [← hresσ, ← hresΔ]
    exact hNumeric c σ hσ

/--
Tail-local copy of the prefix-count `lambda_rho` permutation.

It fixes symbol `0`, sends symbol `1` to the positive stop rank `rho`, shifts
symbols `2,...,rho` down by one, and fixes symbols above `rho`.
-/
def activeTailLambdaRho (T : Nat) (rho : Fin T) (s : Fin T) : Fin T :=
  if _hs0 : s.val = 0 then
    ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le rho.val) rho.isLt⟩
  else if _hs1 : s.val = 1 then
    rho
  else if _hlt : rho.val < s.val then
    s
  else
    ⟨s.val - 1, by omega⟩

def activeTailLambdaRhoInv (T : Nat) (rho : Fin T) (s : Fin T) : Fin T :=
  if _hs0 : s.val = 0 then
    ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le rho.val) rho.isLt⟩
  else if _hlt : s.val < rho.val then
    ⟨s.val + 1, by omega⟩
  else if _heq : s.val = rho.val then
    ⟨1, by omega⟩
  else
    s

theorem activeTailLambdaRhoInv_apply_lambda
    {T : Nat} (rho : Fin T) (hrho : rho.val ≠ 0) :
    ∀ s : Fin T,
      activeTailLambdaRhoInv T rho
          (activeTailLambdaRho T rho s) = s := by
  intro s
  unfold activeTailLambdaRho activeTailLambdaRhoInv
  by_cases hs0 : s.val = 0
  · ext
    simp [hs0]
  · by_cases hs1 : s.val = 1
    · ext
      simp [hs1, hrho]
    · by_cases hlt : rho.val < s.val
      · ext
        have hnot_lt : ¬s.val < rho.val := by omega
        have hne : s.val ≠ rho.val := by omega
        simp [hs0, hs1, hlt, hnot_lt, hne]
      · ext
        have hpred_ne_zero : s.val - 1 ≠ 0 := by omega
        have hpred_lt : s.val - 1 < rho.val := by omega
        simp [hs0, hs1, hlt, hpred_ne_zero, hpred_lt]
        omega

theorem activeTailLambdaRho_apply_inv
    {T : Nat} (rho : Fin T) (hrho : rho.val ≠ 0) :
    ∀ s : Fin T,
      activeTailLambdaRho T rho
          (activeTailLambdaRhoInv T rho s) = s := by
  intro s
  unfold activeTailLambdaRho activeTailLambdaRhoInv
  by_cases hs0 : s.val = 0
  · ext
    simp [hs0]
  · by_cases hlt : s.val < rho.val
    · ext
      have hnot_rho_lt_succ : ¬rho.val < s.val + 1 := by omega
      simp [hs0, hlt, hnot_rho_lt_succ]
    · by_cases heq : s.val = rho.val
      · ext
        simp [heq, hrho]
      · ext
        have hrho_lt : rho.val < s.val := by omega
        have hs_ne_one : s.val ≠ 1 := by omega
        simp [hs0, hlt, heq, hrho_lt, hs_ne_one]

theorem activeTailLambdaRho_val_eq_zero_iff
    {T : Nat} (rho : Fin T) {s : Fin T}
    (hrho : rho.val ≠ 0) :
    (activeTailLambdaRho T rho s).val = 0 ↔ s.val = 0 := by
  constructor
  · intro h
    by_cases hs0 : s.val = 0
    · exact hs0
    · by_cases hs1 : s.val = 1
      · have hval : (activeTailLambdaRho T rho s).val = rho.val := by
          simp [activeTailLambdaRho, hs1]
        exact False.elim (hrho (hval ▸ h))
      · by_cases hlt : rho.val < s.val
        · have hval : activeTailLambdaRho T rho s = s := by
            ext
            simp [activeTailLambdaRho, hs0, hs1, hlt]
          exact (congrArg Fin.val hval).symm ▸ h
        · have hval :
            (activeTailLambdaRho T rho s).val = s.val - 1 := by
            simp [activeTailLambdaRho, hs0, hs1, hlt]
          have hsge : 2 ≤ s.val := by omega
          omega
  · intro hs
    simp [activeTailLambdaRho, hs]

theorem activeTailLambdaRho_val_eq_pos_iff
    {T : Nat} (rho s : Fin T) {l : Nat} (hl : 0 < l) :
    (activeTailLambdaRho T rho s).val = l ↔
      (s.val = 1 ∧ rho.val = l) ∨
        (s.val = l ∧ 1 < s.val ∧ rho.val < s.val) ∨
        (s.val = l + 1 ∧ ¬rho.val < s.val) := by
  by_cases hs0 : s.val = 0
  · have hLambda : (activeTailLambdaRho T rho s).val = 0 := by
      simp [activeTailLambdaRho, hs0]
    constructor
    · intro h
      omega
    · intro hcase
      rcases hcase with ⟨hs, _⟩ | ⟨hs, hspos, _⟩ | ⟨hs, _⟩ <;> omega
  · by_cases hs1 : s.val = 1
    · have hLambda : (activeTailLambdaRho T rho s).val = rho.val := by
        simp [activeTailLambdaRho, hs1]
      constructor
      · intro h
        exact Or.inl ⟨hs1, by omega⟩
      · intro hcase
        rcases hcase with ⟨_hs, hrho⟩ | ⟨hs, hspos, _⟩ | ⟨hs, _⟩
        · omega
        · omega
        · omega
    · by_cases hlt : rho.val < s.val
      · have hLambda : (activeTailLambdaRho T rho s).val = s.val := by
          simp [activeTailLambdaRho, hs0, hs1, hlt]
        constructor
        · intro h
          rw [hLambda] at h
          exact Or.inr (Or.inl ⟨by omega, by omega, hlt⟩)
        · intro hcase
          rw [hLambda]
          rcases hcase with ⟨hs, _⟩ | ⟨hs, _hspos, _hrho⟩ | ⟨hs, _⟩
          · omega
          · exact hs
          · omega
      · have hLambda : (activeTailLambdaRho T rho s).val = s.val - 1 := by
          simp [activeTailLambdaRho, hs0, hs1, hlt]
        constructor
        · intro h
          rw [hLambda] at h
          exact Or.inr (Or.inr ⟨by omega, hlt⟩)
        · intro hcase
          rw [hLambda]
          rcases hcase with ⟨hs, _⟩ | ⟨_hs, _hspos, hrho⟩ | ⟨hs, _hrho⟩
          · omega
          · exact False.elim (hlt hrho)
          · omega

theorem activeTailLambdaRho_bijective
    {T : Nat} (rho : Fin T) (hrho : rho.val ≠ 0) :
    Function.Bijective (activeTailLambdaRho T rho) := by
  constructor
  · intro a b hab
    have h := congrArg (activeTailLambdaRhoInv T rho) hab
    simpa [activeTailLambdaRhoInv_apply_lambda rho hrho] using h
  · intro s
    refine ⟨activeTailLambdaRhoInv T rho s, ?_⟩
    exact activeTailLambdaRho_apply_inv rho hrho s

noncomputable def activeTailLambdaRhoEquiv
    {T : Nat} (rho : Fin T) (hrho : rho.val ≠ 0) : Fin T ≃ Fin T :=
  Equiv.ofBijective (activeTailLambdaRho T rho)
    (activeTailLambdaRho_bijective rho hrho)

@[simp] theorem activeTailLambdaRhoEquiv_apply
    {T : Nat} (rho : Fin T) (hrho : rho.val ≠ 0) (s : Fin T) :
    activeTailLambdaRhoEquiv rho hrho s = activeTailLambdaRho T rho s := rfl

def activeTailCanonicalRhoHitNat {m n : Nat}
    (z : Fin n → ZMod m) (j : Nat) : Prop :=
  ∃ hj : j < n, j + 1 < n ∧ z ⟨j, hj⟩ = 0

noncomputable def activeTailCanonicalRhoFirstNat {m n : Nat}
    (z : Fin n → ZMod m)
    (h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j) : Nat := by
  classical
  exact Nat.find h

theorem activeTailCanonicalRhoFirstNat_spec {m n : Nat}
    {z : Fin n → ZMod m}
    (h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j) :
    activeTailCanonicalRhoHitNat z
      (activeTailCanonicalRhoFirstNat z h) := by
  classical
  unfold activeTailCanonicalRhoFirstNat
  exact Nat.find_spec h

theorem activeTailCanonicalRhoFirstNat_minimal {m n : Nat}
    {z : Fin n → ZMod m}
    (h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j)
    {j : Nat} (hj : activeTailCanonicalRhoHitNat z j) :
    activeTailCanonicalRhoFirstNat z h ≤ j := by
  classical
  unfold activeTailCanonicalRhoFirstNat
  exact Nat.find_min' h hj

noncomputable def activeTailCanonicalRho {m n : Nat} (_hT : 2 ≤ n + 1)
    (z : Fin n → ZMod m) : Fin (n + 1) := by
  classical
  exact
    if h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j then
      ⟨activeTailCanonicalRhoFirstNat z h + 1, by
        rcases activeTailCanonicalRhoFirstNat_spec h with ⟨hj, hlt, hz⟩
        omega⟩
    else
      Fin.last n

theorem activeTailCanonicalRho_ne_zero {m n : Nat} (hT : 2 ≤ n + 1)
    (z : Fin n → ZMod m) :
    (activeTailCanonicalRho hT z).val ≠ 0 := by
  classical
  unfold activeTailCanonicalRho
  by_cases h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j
  · simp [h]
  · have hnpos : 0 < n := by omega
    simpa [h, Fin.last] using hnpos.ne'

theorem activeTailCanonicalRho_val_eq_find_succ {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    (h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j) :
    (activeTailCanonicalRho hT z).val =
      activeTailCanonicalRhoFirstNat z h + 1 := by
  classical
  unfold activeTailCanonicalRho
  simp [h]

theorem activeTailCanonicalRho_eq_last_of_no_hit {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    (h : ¬ ∃ j : Nat, activeTailCanonicalRhoHitNat z j) :
    activeTailCanonicalRho hT z = Fin.last n := by
  classical
  unfold activeTailCanonicalRho
  simp [h]

theorem activeTailCanonicalRho_val_lt_iff_exists_hit_before {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m} {q : Nat}
    (hq : q ≤ n) :
    (activeTailCanonicalRho hT z).val < q ↔
      ∃ j : Nat, j + 1 < q ∧ activeTailCanonicalRhoHitNat z j := by
  classical
  by_cases h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j
  · rw [activeTailCanonicalRho_val_eq_find_succ hT h]
    constructor
    · intro hrho
      exact ⟨activeTailCanonicalRhoFirstNat z h, hrho,
        activeTailCanonicalRhoFirstNat_spec h⟩
    · intro hex
      rcases hex with ⟨j, hjlt, hj⟩
      have hmin := activeTailCanonicalRhoFirstNat_minimal h hj
      omega
  · have hlast := activeTailCanonicalRho_eq_last_of_no_hit hT h
    constructor
    · intro hrho
      have hnlt : ¬ n < q := by omega
      exact False.elim (hnlt (by simpa [hlast, Fin.last] using hrho))
    · intro hex
      rcases hex with ⟨j, _hjlt, hj⟩
      exact False.elim (h ⟨j, hj⟩)

theorem activeTailCanonicalRho_val_lt_congr_of_agree_before
    {m n : Nat} (hT : 2 ≤ n + 1) {z w : Fin n → ZMod m}
    {q : Nat} (hq : q ≤ n)
    (hagree : ∀ j : Fin n, j.val + 1 < q → z j = w j) :
    (activeTailCanonicalRho hT z).val < q ↔
      (activeTailCanonicalRho hT w).val < q := by
  classical
  rw [activeTailCanonicalRho_val_lt_iff_exists_hit_before hT hq,
    activeTailCanonicalRho_val_lt_iff_exists_hit_before hT hq]
  constructor
  · intro hex
    rcases hex with ⟨j, hjlt, hj⟩
    rcases hj with ⟨hjn, hjpred, hz⟩
    exact ⟨j, hjlt, ⟨hjn, hjpred, by
      rw [← hagree ⟨j, hjn⟩ hjlt]
      exact hz⟩⟩
  · intro hex
    rcases hex with ⟨j, hjlt, hj⟩
    rcases hj with ⟨hjn, hjpred, hw⟩
    exact ⟨j, hjlt, ⟨hjn, hjpred, by
      rw [hagree ⟨j, hjn⟩ hjlt]
      exact hw⟩⟩

theorem activeTailCanonicalRho_val_lt_add_single_iff
    {m n : Nat} (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    {q : Nat} (hq : q ≤ n) {σ : Fin n} (hσ : q ≤ σ.val + 1) :
    (activeTailCanonicalRho hT
        (fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0)).val < q
      ↔
    (activeTailCanonicalRho hT z).val < q := by
  refine
    activeTailCanonicalRho_val_lt_congr_of_agree_before
      hT hq ?_
  intro j hj
  have hne : j ≠ σ := by
    intro h
    have : σ.val + 1 < q := by
      simpa [h] using hj
    omega
  simp [hne]

theorem activeTailCanonicalRho_val_lt_sub_single_iff
    {m n : Nat} (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    {q : Nat} (hq : q ≤ n) {σ : Fin n} (hσ : q ≤ σ.val + 1) :
    (activeTailCanonicalRho hT
        (fun τ : Fin n => z τ - if τ = σ then (1 : ZMod m) else 0)).val < q
      ↔
    (activeTailCanonicalRho hT z).val < q := by
  refine
    activeTailCanonicalRho_val_lt_congr_of_agree_before
      hT hq ?_
  intro j hj
  have hne : j ≠ σ := by
    intro h
    have : σ.val + 1 < q := by
      simpa [h] using hj
    omega
  simp [hne]

theorem activeTailCanonicalRho_last_iff {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m} :
    (activeTailCanonicalRho hT z).val = n ↔
      ∀ j : Fin n, j.val + 1 < n → z j ≠ 0 := by
  classical
  constructor
  · intro hrho j hjlt hz
    have hhit : activeTailCanonicalRhoHitNat z j.val :=
      ⟨j.isLt, hjlt, hz⟩
    by_cases h : ∃ q : Nat, activeTailCanonicalRhoHitNat z q
    · have hmin := activeTailCanonicalRhoFirstNat_minimal h hhit
      have hval := activeTailCanonicalRho_val_eq_find_succ hT h
      omega
    · exact h ⟨j.val, hhit⟩
  · intro hno
    by_cases h : ∃ q : Nat, activeTailCanonicalRhoHitNat z q
    · rcases activeTailCanonicalRhoFirstNat_spec h with ⟨hj, hlt, hz⟩
      exact False.elim (hno ⟨activeTailCanonicalRhoFirstNat z h, hj⟩ hlt hz)
    · have hlast := activeTailCanonicalRho_eq_last_of_no_hit hT h
      simpa [hlast, Fin.last]

theorem activeTailCanonicalRho_pred_hitNat {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    (hρ : (activeTailCanonicalRho hT z).val < n) :
    activeTailCanonicalRhoHitNat z
      ((activeTailCanonicalRho hT z).val - 1) := by
  classical
  by_cases h : ∃ j : Nat, activeTailCanonicalRhoHitNat z j
  · have hspec := activeTailCanonicalRhoFirstNat_spec h
    have hval := activeTailCanonicalRho_val_eq_find_succ hT h
    have heq :
        activeTailCanonicalRhoFirstNat z h =
          (activeTailCanonicalRho hT z).val - 1 := by
      omega
    simpa [heq] using hspec
  · have hlast := activeTailCanonicalRho_eq_last_of_no_hit hT h
    have hn : (activeTailCanonicalRho hT z).val = n := by
      simpa [hlast, Fin.last]
    omega

theorem activeTailCanonicalRho_no_hit_before {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    {j : Nat}
    (hj : j + 1 < (activeTailCanonicalRho hT z).val) :
    ¬ activeTailCanonicalRhoHitNat z j := by
  classical
  intro hhit
  by_cases h : ∃ q : Nat, activeTailCanonicalRhoHitNat z q
  · have hmin := activeTailCanonicalRhoFirstNat_minimal h hhit
    have hval := activeTailCanonicalRho_val_eq_find_succ hT h
    omega
  · exact h ⟨j, hhit⟩

theorem activeTailCanonicalRho_update_at_rho {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    (hρ : (activeTailCanonicalRho hT z).val < n)
    (δ : ZMod m) :
    activeTailCanonicalRho hT
        (fun τ : Fin n =>
          z τ +
            if τ =
              ⟨(activeTailCanonicalRho hT z).val, hρ⟩
            then δ else 0)
      =
    activeTailCanonicalRho hT z := by
  classical
  let ρ := activeTailCanonicalRho hT z
  let j0 : Nat := ρ.val - 1
  have hρnz : ρ.val ≠ 0 := by
    simpa [ρ] using activeTailCanonicalRho_ne_zero hT z
  have hj0_lt : j0 < n := by
    omega
  have hj0_succ_lt : j0 + 1 < n := by
    omega
  have hj0_succ : j0 + 1 = ρ.val := by
    omega
  have hhit_z : activeTailCanonicalRhoHitNat z j0 := by
    simpa [ρ, j0] using activeTailCanonicalRho_pred_hitNat hT hρ
  let w : Fin n → ZMod m := fun τ =>
    z τ + if τ = ⟨ρ.val, by simpa [ρ] using hρ⟩ then δ else 0
  have hhit_w : activeTailCanonicalRhoHitNat w j0 := by
    rcases hhit_z with ⟨hj, hlt, hz⟩
    refine ⟨hj, hlt, ?_⟩
    have hne :
        (⟨j0, hj⟩ : Fin n) ≠
          ⟨ρ.val, by simpa [ρ] using hρ⟩ := by
      intro h
      have hval := congrArg Fin.val h
      have hval' : j0 = ρ.val := by
        simpa using hval
      have : j0 + 1 = ρ.val := hj0_succ
      omega
    simp [w, hne, hz]
  have hwexists : ∃ j : Nat, activeTailCanonicalRhoHitNat w j :=
    ⟨j0, hhit_w⟩
  have hfind_le :
      activeTailCanonicalRhoFirstNat w hwexists ≤ j0 :=
    activeTailCanonicalRhoFirstNat_minimal hwexists hhit_w
  have hfind_ge :
      j0 ≤ activeTailCanonicalRhoFirstNat w hwexists := by
    by_contra hnot
    have hlt : activeTailCanonicalRhoFirstNat w hwexists < j0 := by
      omega
    have hspec := activeTailCanonicalRhoFirstNat_spec hwexists
    rcases hspec with ⟨hj, hpred, hwzero⟩
    have hne :
        (⟨activeTailCanonicalRhoFirstNat w hwexists, hj⟩ : Fin n) ≠
          ⟨ρ.val, by simpa [ρ] using hρ⟩ := by
      intro h
      have hval := congrArg Fin.val h
      have hval' :
          activeTailCanonicalRhoFirstNat w hwexists = ρ.val := by
        simpa using hval
      have hltρ :
          activeTailCanonicalRhoFirstNat w hwexists < ρ.val := by
        omega
      omega
    have hz_hit :
        activeTailCanonicalRhoHitNat z
          (activeTailCanonicalRhoFirstNat w hwexists) := by
      refine ⟨hj, hpred, ?_⟩
      have hwcoord :
          w ⟨activeTailCanonicalRhoFirstNat w hwexists, hj⟩ =
            z ⟨activeTailCanonicalRhoFirstNat w hwexists, hj⟩ := by
        simp [w, hne]
      rw [← hwcoord]
      exact hwzero
    have hbefore :
        activeTailCanonicalRhoFirstNat w hwexists + 1 < ρ.val := by
      omega
    exact
      (activeTailCanonicalRho_no_hit_before hT (z := z)
        (j := activeTailCanonicalRhoFirstNat w hwexists)
        (by simpa [ρ] using hbefore)) hz_hit
  have hfind :
      activeTailCanonicalRhoFirstNat w hwexists = j0 := by
    omega
  apply Fin.ext
  have hval_w := activeTailCanonicalRho_val_eq_find_succ hT hwexists
  simp [w] at hval_w
  calc
    (activeTailCanonicalRho hT w).val
        = activeTailCanonicalRhoFirstNat w hwexists + 1 := hval_w
    _ = j0 + 1 := by rw [hfind]
    _ = ρ.val := by omega
    _ = (activeTailCanonicalRho hT z).val := rfl

theorem activeTailCanonicalRho_add_at_rho {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    (hρ : (activeTailCanonicalRho hT z).val < n) :
    activeTailCanonicalRho hT
        (fun τ : Fin n =>
          z τ +
            if τ =
              ⟨(activeTailCanonicalRho hT z).val, hρ⟩
            then (1 : ZMod m) else 0)
      =
    activeTailCanonicalRho hT z :=
  activeTailCanonicalRho_update_at_rho hT hρ 1

theorem activeTailCanonicalRho_sub_at_rho {m n : Nat}
    (hT : 2 ≤ n + 1) {z : Fin n → ZMod m}
    (hρ : (activeTailCanonicalRho hT z).val < n) :
    activeTailCanonicalRho hT
        (fun τ : Fin n =>
          z τ -
            if τ =
              ⟨(activeTailCanonicalRho hT z).val, hρ⟩
            then (1 : ZMod m) else 0)
      =
    activeTailCanonicalRho hT z := by
  convert activeTailCanonicalRho_update_at_rho hT hρ (-(1 : ZMod m)) using 2
  funext τ
  by_cases hτ :
      τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
  · simp [hτ, sub_eq_add_neg]
  · simp [hτ]

theorem activeTailCanonicalRho_dynamic_add_bijective {m n : Nat}
    (hT : 2 ≤ n + 1) :
    Function.Bijective
      (fun z : Fin n → ZMod m =>
        fun τ : Fin n =>
          if hρ : (activeTailCanonicalRho hT z).val < n then
            z τ +
              if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
              then (1 : ZMod m) else 0
          else z τ) := by
  classical
  let F : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if hρ : (activeTailCanonicalRho hT z).val < n then
        z τ +
          if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
          then (1 : ZMod m) else 0
      else z τ
  let G : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if hρ : (activeTailCanonicalRho hT z).val < n then
        z τ -
          if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
          then (1 : ZMod m) else 0
      else z τ
  have hleft : Function.LeftInverse G F := by
    intro z
    funext τ
    by_cases hρ : (activeTailCanonicalRho hT z).val < n
    · have hF :
          F z =
            (fun τ : Fin n =>
              z τ +
                if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
                then (1 : ZMod m) else 0) := by
        funext τ
        simp [F, hρ]
      have hpres :
          activeTailCanonicalRho hT (F z) =
            activeTailCanonicalRho hT z := by
        rw [hF]
        exact activeTailCanonicalRho_add_at_rho hT hρ
      have hρF : (activeTailCanonicalRho hT (F z)).val < n := by
        simpa [hpres] using hρ
      have hidx :
          (⟨(activeTailCanonicalRho hT (F z)).val, hρF⟩ : Fin n) =
            ⟨(activeTailCanonicalRho hT z).val, hρ⟩ := by
        ext
        simp [hpres]
      calc
        G (F z) τ =
            F z τ -
              if τ = ⟨(activeTailCanonicalRho hT (F z)).val, hρF⟩
              then (1 : ZMod m) else 0 := by
                simp [G, hρF]
        _ =
            (z τ +
              if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
              then (1 : ZMod m) else 0) -
              if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
              then (1 : ZMod m) else 0 := by
                have hFτ := congrFun hF τ
                rw [hFτ, hidx]
        _ = z τ := by
              by_cases hτ :
                  τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
    · have hF : F z = z := by
        funext τ
        simp [F, hρ]
      have hρF : ¬ (activeTailCanonicalRho hT (F z)).val < n := by
        simpa [hF] using hρ
      calc
        G (F z) τ = F z τ := by
          simp [G, hρF]
        _ = z τ := by rw [hF]
  have hright : Function.RightInverse G F := by
    intro z
    funext τ
    by_cases hρ : (activeTailCanonicalRho hT z).val < n
    · have hG :
          G z =
            (fun τ : Fin n =>
              z τ -
                if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
                then (1 : ZMod m) else 0) := by
        funext τ
        simp [G, hρ]
      have hpres :
          activeTailCanonicalRho hT (G z) =
            activeTailCanonicalRho hT z := by
        rw [hG]
        exact activeTailCanonicalRho_sub_at_rho hT hρ
      have hρG : (activeTailCanonicalRho hT (G z)).val < n := by
        simpa [hpres] using hρ
      have hidx :
          (⟨(activeTailCanonicalRho hT (G z)).val, hρG⟩ : Fin n) =
            ⟨(activeTailCanonicalRho hT z).val, hρ⟩ := by
        ext
        simp [hpres]
      calc
        F (G z) τ =
            G z τ +
              if τ = ⟨(activeTailCanonicalRho hT (G z)).val, hρG⟩
              then (1 : ZMod m) else 0 := by
                simp [F, hρG]
        _ =
            (z τ -
              if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
              then (1 : ZMod m) else 0) +
              if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
              then (1 : ZMod m) else 0 := by
                have hGτ := congrFun hG τ
                rw [hGτ, hidx]
        _ = z τ := by
              by_cases hτ :
                  τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
    · have hG : G z = z := by
        funext τ
        simp [G, hρ]
      have hρG : ¬ (activeTailCanonicalRho hT (G z)).val < n := by
        simpa [hG] using hρ
      calc
        F (G z) τ = G z τ := by
          simp [F, hρG]
        _ = z τ := by rw [hG]
  exact ⟨hleft.injective, hright.surjective⟩

noncomputable def activePrefixTailPerm
    {b m n : Nat} [NeZero m] (hT : 2 ≤ n + 1) :
    Shared.TorusVertex (b + 1) m →
      (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)) :=
  fun _y z =>
    activeTailLambdaRhoEquiv
      (activeTailCanonicalRho hT z)
      (activeTailCanonicalRho_ne_zero hT z)

@[simp] theorem activePrefixTailPerm_apply
    {b m n : Nat} [NeZero m] (hT : 2 ≤ n + 1)
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (s : Fin (n + 1)) :
    activePrefixTailPerm (b := b) (m := m) hT y z s =
      activeTailLambdaRho (n + 1) (activeTailCanonicalRho hT z) s := rfl

/--
The local geometric assembly theorem still needed for the primitive lift.

This deliberately omits packet arithmetic, slack, and the solved base
hypothesis: those are used to construct the cylinder and its primitive active
symboling.  Once those objects exist, the remaining content is to expand the
compressed base-tail cylinder into a Cayley Hamilton decomposition in dimension
`b + T`.
-/
def PrimitiveActiveLiftAssemblyGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T),
      IsCylinder Cyl →
      IsPrimitiveActiveSymboling hT A →
      Shared.CayleyHamiltonDecomposition (b + T) m

/--
Primitive lift target in the form matching the v2 base-tail architecture.

The active Hall layer supplies only symbol counts.  Those counts must feed an
extended prefix-count tail theorem for arbitrary threshold-symbol words; the
full-vertex lift should consume the count primitiveity stated here, rather than
the diagnostic `expandedColorDir` Hamiltonian route below.
-/
def PrimitiveActivePrefixLiftAssemblyGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T),
      IsCylinder Cyl →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      Shared.CayleyHamiltonDecomposition (b + T) m

structure PrefixProjectedLiftColorDir {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets) where
  colorDir :
    Shared.TorusColor (b + T) →
      Shared.TorusVertex (b + T) m →
      Shared.TorusDirection (b + T)
  edgePartition : Shared.IsCayleyEdgePartition colorDir
  colorHamiltonian : Shared.IsCayleyColorHamiltonian colorDir
  collapse_step :
    ∀ c : Fin (b + T), ∀ x : Shared.TorusVertex (b + T) m,
      collapseVertex b m T (Shared.cayleyColorStep colorDir c x) =
        Cyl.step c (collapseVertex b m T x)

/--
Projected lift data before Hamiltonicity is proved.

The useful primitive-lift interface is not just an expanded edge selector: the
expanded step must be a skew product over the compressed cylinder after the
collapse/fiber coordinate split.  Hamiltonicity can then be proved from the
section return on the fiber.
-/
structure PrefixProjectedLiftColorDirCore {b m n : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m (n + 1) packets) where
  colorDir :
    Shared.TorusColor (b + (n + 1)) →
      Shared.TorusVertex (b + (n + 1)) m →
        Shared.TorusDirection (b + (n + 1))
  edgePartition : Shared.IsCayleyEdgePartition colorDir
  collapse_step :
    ∀ c : Fin (b + (n + 1)),
      ∀ x : Shared.TorusVertex (b + (n + 1)) m,
        collapseVertex b m (n + 1) (Shared.cayleyColorStep colorDir c x) =
          Cyl.step c (collapseVertex b m (n + 1) x)

namespace PrefixProjectedLiftColorDirCore

noncomputable def fiberStep {b m n : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m (n + 1) packets}
    (D : PrefixProjectedLiftColorDirCore Cyl)
    (c : Fin (b + (n + 1))) :
    Shared.TorusVertex (b + 1) m →
      (Fin n → ZMod m) → (Fin n → ZMod m) :=
  fun y z =>
    (collapseVertexFiberEquiv b m n
      (Shared.cayleyColorStep D.colorDir c
        ((collapseVertexFiberEquiv b m n).symm (y, z)))).2

theorem skew_conj {b m n : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m (n + 1) packets}
    (D : PrefixProjectedLiftColorDirCore Cyl)
    (c : Fin (b + (n + 1)))
    (p : Shared.TorusVertex (b + 1) m × (Fin n → ZMod m)) :
    collapseVertexFiberEquiv b m n
        (Shared.cayleyColorStep D.colorDir c
          ((collapseVertexFiberEquiv b m n).symm p))
      =
    Shared.skewProductMap (Cyl.step c) (D.fiberStep c) p := by
  rcases p with ⟨y, z⟩
  apply Prod.ext
  · dsimp [Shared.skewProductMap, fiberStep]
    change
      collapseVertex b m (n + 1)
          (Shared.cayleyColorStep D.colorDir c
            ((collapseVertexFiberEquiv b m n).symm (y, z))) =
        Cyl.step c y
    rw [D.collapse_step]
    have hy :
        collapseVertex b m (n + 1)
          ((collapseVertexFiberEquiv b m n).symm (y, z)) = y := by
      have h :=
        congrArg Prod.fst
          ((collapseVertexFiberEquiv b m n).right_inv (y, z))
      exact h
    rw [hy]
  · rfl

theorem fiberStep_of_tail_castSucc {b m n : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m (n + 1) packets}
    (D : PrefixProjectedLiftColorDirCore Cyl)
    (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (σ : Fin n)
    (hcolor :
      D.colorDir c ((collapseVertexFiberEquiv b m n).symm (y, z)) =
        tailExpandedDir b σ.castSucc) :
    D.fiberStep c y z =
      fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0 := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hcolor' :
      D.colorDir c x = tailExpandedDir b σ.castSucc := by
    simpa [x] using hcolor
  have hfiber :=
    congrArg Prod.snd
      (collapseVertexFiberEquiv_add_tailExpandedDir_castSucc
        (b := b) (m := m) (n := n) x σ)
  calc
    D.fiberStep c y z
        =
      (collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b σ.castSucc))).2 := by
        simp [PrefixProjectedLiftColorDirCore.fiberStep,
          Shared.cayleyColorStep, x, hcolor']
    _ =
      (fun τ : Fin n =>
        collapseFiberInit b m n x τ +
          if τ = σ then (1 : ZMod m) else 0) := by
        simpa using hfiber
    _ = (fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0) := by
        funext τ
        rw [hz]

theorem fiberStep_of_tail_last {b m n : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m (n + 1) packets}
    (D : PrefixProjectedLiftColorDirCore Cyl)
    (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (hcolor :
      D.colorDir c ((collapseVertexFiberEquiv b m n).symm (y, z)) =
        tailExpandedDir b (Fin.last n)) :
    D.fiberStep c y z = z := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hcolor' :
      D.colorDir c x = tailExpandedDir b (Fin.last n) := by
    simpa [x] using hcolor
  have hfiber :=
    congrArg Prod.snd
      (collapseVertexFiberEquiv_add_tailExpandedDir_last
        (b := b) (m := m) (n := n) x)
  calc
    D.fiberStep c y z
        =
      (collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b (Fin.last n)))).2 := by
        simp [PrefixProjectedLiftColorDirCore.fiberStep,
          Shared.cayleyColorStep, x, hcolor']
    _ = collapseFiberInit b m n x := by
        simpa using hfiber
    _ = z := hz

theorem fiberStep_of_ordinaryExpandedDir {b m n : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m (n + 1) packets}
    (D : PrefixProjectedLiftColorDirCore Cyl)
    (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (i : Fin (b + 1)) (hdir : i ≠ activeDir b)
    (hcolor :
      D.colorDir c ((collapseVertexFiberEquiv b m n).symm (y, z)) =
        ordinaryExpandedDir i hdir) :
    D.fiberStep c y z = z := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hcolor' :
      D.colorDir c x = ordinaryExpandedDir i hdir := by
    simpa [x] using hcolor
  have hfiber :=
    congrArg Prod.snd
      (collapseVertexFiberEquiv_add_ordinaryExpandedDir
        (b := b) (m := m) (n := n) x i hdir)
  calc
    D.fiberStep c y z
        =
      (collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (ordinaryExpandedDir i hdir))).2 := by
        simp [PrefixProjectedLiftColorDirCore.fiberStep,
          Shared.cayleyColorStep, x, hcolor']
    _ = collapseFiberInit b m n x := by
        simpa using hfiber
    _ = z := hz

end PrefixProjectedLiftColorDirCore

noncomputable def activePermutedColorDirCore
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m (n + 1) packets)
    (A : ActiveSymboling Cyl)
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (hCyl : IsCylinder Cyl) :
    PrefixProjectedLiftColorDirCore Cyl where
  colorDir := activePermutedColorDir Cyl A tailPerm
  edgePartition := activePermutedColorDirEdgePartition tailPerm hCyl
  collapse_step := by
    intro c x
    exact collapseVertex_cayleyColorStep_activePermutedColorDir
      Cyl A tailPerm c x

theorem activePermutedColorDirCore_fiberStep_of_inactive
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (hactive : Cyl.dir c y ≠ activeDir b) :
    (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z = z := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hy :
      collapseVertex b m (n + 1) x = y := by
    have h :=
      congrArg Prod.fst
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hactive_x :
      Cyl.dir c (collapseVertex b m (n + 1) x) ≠ activeDir b := by
    simpa [hy] using hactive
  have hcolor :
      activePermutedColorDir Cyl A tailPerm c x =
        ordinaryExpandedDir (Cyl.dir c y) hactive := by
    simp [activePermutedColorDir, x, hy, hactive]
  exact
    PrefixProjectedLiftColorDirCore.fiberStep_of_ordinaryExpandedDir
      (activePermutedColorDirCore Cyl A tailPerm hCyl)
      c y z (Cyl.dir c y) hactive hcolor

theorem activePermutedColorDirCore_fiberStep_of_active_castSucc
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (σ : Fin n)
    (hactive : Cyl.dir c y = activeDir b)
    (hsym :
      (tailPerm y z)
        ((A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y})) =
        σ.castSucc) :
    (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z =
      fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0 := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hy :
      collapseVertex b m (n + 1) x = y := by
    have h :=
      congrArg Prod.fst
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hactive_x :
      Cyl.dir c (collapseVertex b m (n + 1) x) = activeDir b := by
    simpa [hy] using hactive
  have hmem_x : c ∈ Cyl.active (collapseVertex b m (n + 1) x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive_x⟩
  have hmem_y : c ∈ Cyl.active y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
  have hsym_base :
      (A.Φ.equiv (collapseVertex b m (n + 1) x)).symm
          (⟨c, by
            change c ∈ Cyl.active (collapseVertex b m (n + 1) x)
            exact hmem_x⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active
                (collapseVertex b m (n + 1) x)}) =
        (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact hmem_y⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}) :=
    activeSymboling_symm_congr (A := A) hy hmem_x hmem_y
  have hcolor :
      activePermutedColorDir Cyl A tailPerm c x =
        tailExpandedDir b σ.castSucc := by
    calc
      activePermutedColorDir Cyl A tailPerm c x =
          tailExpandedDir b
            ((tailPerm y z)
              ((A.Φ.equiv y).symm
                (⟨c, by
                  change c ∈ Cyl.active y
                  exact hmem_y⟩ :
                  {c : Fin (b + (n + 1)) //
                    c ∈ (Cyl.incidence).active y}))) := by
        simp [activePermutedColorDir, x, hy, hz, hactive, hsym_base]
      _ = tailExpandedDir b σ.castSucc := by
        rw [hsym]
  exact
    PrefixProjectedLiftColorDirCore.fiberStep_of_tail_castSucc
      (activePermutedColorDirCore Cyl A tailPerm hCyl)
      c y z σ hcolor

theorem activePermutedColorDirCore_fiberStep_of_active_last
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (hactive : Cyl.dir c y = activeDir b)
    (hsym :
      (tailPerm y z)
        ((A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y})) =
        Fin.last n) :
    (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z = z := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hy :
      collapseVertex b m (n + 1) x = y := by
    have h :=
      congrArg Prod.fst
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hactive_x :
      Cyl.dir c (collapseVertex b m (n + 1) x) = activeDir b := by
    simpa [hy] using hactive
  have hmem_x : c ∈ Cyl.active (collapseVertex b m (n + 1) x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive_x⟩
  have hmem_y : c ∈ Cyl.active y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
  have hsym_base :
      (A.Φ.equiv (collapseVertex b m (n + 1) x)).symm
          (⟨c, by
            change c ∈ Cyl.active (collapseVertex b m (n + 1) x)
            exact hmem_x⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active
                (collapseVertex b m (n + 1) x)}) =
        (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact hmem_y⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}) :=
    activeSymboling_symm_congr (A := A) hy hmem_x hmem_y
  have hcolor :
      activePermutedColorDir Cyl A tailPerm c x =
        tailExpandedDir b (Fin.last n) := by
    calc
      activePermutedColorDir Cyl A tailPerm c x =
          tailExpandedDir b
            ((tailPerm y z)
              ((A.Φ.equiv y).symm
                (⟨c, by
                  change c ∈ Cyl.active y
                  exact hmem_y⟩ :
                  {c : Fin (b + (n + 1)) //
                    c ∈ (Cyl.incidence).active y}))) := by
        simp [activePermutedColorDir, x, hy, hz, hactive, hsym_base]
      _ = tailExpandedDir b (Fin.last n) := by
        rw [hsym]
  exact
    PrefixProjectedLiftColorDirCore.fiberStep_of_tail_last
      (activePermutedColorDirCore Cyl A tailPerm hCyl)
      c y z hcolor

noncomputable def activePermutedColorDirCoreDirectCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} (A : ActiveSymboling Cyl)
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (c : Fin (b + (n + 1))) (y : Shared.TorusVertex (b + 1) m)
    (z : Fin n → ZMod m) (τ : Fin n) : ZMod m :=
  if hactive : Cyl.dir c y = activeDir b then
    if
      (tailPerm y z)
        ((A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y})) =
        τ.castSucc
    then 1
    else 0
  else 0

theorem activePermutedColorDirCore_fiberStep_coord_eq_add_directCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (τ : Fin n) :
    (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z τ =
      z τ + activePermutedColorDirCoreDirectCarry A tailPerm c y z τ := by
  classical
  by_cases hactive : Cyl.dir c y = activeDir b
  · let activeSymbol : Fin (n + 1) :=
      (tailPerm y z)
        ((A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}))
    by_cases hτσ : activeSymbol = τ.castSucc
    · have hstep :=
        activePermutedColorDirCore_fiberStep_of_active_castSucc
          tailPerm hCyl c y z τ hactive (by
            simpa [activeSymbol] using hτσ)
      calc
        (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z τ
            =
          (fun υ : Fin n =>
            z υ + if υ = τ then (1 : ZMod m) else 0) τ := by
            exact congrFun hstep τ
        _ = z τ + activePermutedColorDirCoreDirectCarry A tailPerm c y z τ := by
            simp [activePermutedColorDirCoreDirectCarry, hactive,
              activeSymbol, hτσ]
    · rcases Fin.eq_castSucc_or_eq_last activeSymbol with ⟨σ, hσ⟩ | hlast
      · have hne : τ ≠ σ := by
          intro h
          apply hτσ
          rw [h, hσ]
        have hstep :=
          activePermutedColorDirCore_fiberStep_of_active_castSucc
            tailPerm hCyl c y z σ hactive (by
              simpa [activeSymbol] using hσ)
        calc
          (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z τ
              =
            (fun υ : Fin n =>
              z υ + if υ = σ then (1 : ZMod m) else 0) τ := by
              exact congrFun hstep τ
          _ = z τ + activePermutedColorDirCoreDirectCarry A tailPerm c y z τ := by
              simp [activePermutedColorDirCoreDirectCarry, hactive,
                activeSymbol, hσ, hne, hne.symm]
      · have hcarry :
            activePermutedColorDirCoreDirectCarry A tailPerm c y z τ = 0 := by
          have hnot :
              (tailPerm y z)
                  ((A.Φ.equiv y).symm
                    (⟨c, by
                      change c ∈ Cyl.active y
                      exact
                        Finset.mem_filter.mpr
                          ⟨Finset.mem_univ c, hactive⟩⟩ :
                      {c : Fin (b + (n + 1)) //
                        c ∈ (Cyl.incidence).active y})) ≠
                τ.castSucc := by
            simpa [activeSymbol] using hτσ
          simp [activePermutedColorDirCoreDirectCarry, hactive, hnot]
        have hstep :=
          activePermutedColorDirCore_fiberStep_of_active_last
            tailPerm hCyl c y z hactive (by
              simpa [activeSymbol] using hlast)
        calc
          (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z τ
              = z τ := by
              exact congrFun hstep τ
          _ = z τ + activePermutedColorDirCoreDirectCarry A tailPerm c y z τ := by
              rw [hcarry, add_zero]
  · have hstep :=
      activePermutedColorDirCore_fiberStep_of_inactive (A := A)
        tailPerm hCyl c y z hactive
    calc
      (activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y z τ
          = z τ := by
          exact congrFun hstep τ
      _ = z τ + activePermutedColorDirCoreDirectCarry A tailPerm c y z τ := by
          simp [activePermutedColorDirCoreDirectCarry, hactive]

theorem activePermutedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (tailPerm :
      Shared.TorusVertex (b + 1) m →
        (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1)))
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (base : Shared.TorusVertex (b + 1) m) (period : Nat)
    (z : Fin n → ZMod m) (τ : Fin n) :
    Shared.sectionReturn
        (Shared.skewProductMap
          (Cyl.step c)
          ((activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c))
        base period z τ =
      z τ +
        ∑ u ∈ Finset.range period,
          activePermutedColorDirCoreDirectCarry A tailPerm c
            (((Cyl.step c)^[u]) base)
            (Shared.skewFiberIterate
              (Cyl.step c)
              ((activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c)
              u base z)
            τ := by
  classical
  rw [Shared.sectionReturn_skewProductMap_eq_fiberIterate]
  exact
    Shared.skewFiberIterate_coord_eq_add_sum_range
      (Cyl.step c)
      ((activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c)
      (fun y fiber =>
        activePermutedColorDirCoreDirectCarry A tailPerm c y fiber τ)
      τ
      (by
        intro y fiber
        exact activePermutedColorDirCore_fiberStep_coord_eq_add_directCarry
          tailPerm hCyl c y fiber τ)
      period base z

noncomputable def activePrefixPermutedColorDirCore
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m (n + 1) packets)
    (A : ActiveSymboling Cyl)
    (hT : 2 ≤ n + 1) (hCyl : IsCylinder Cyl) :
    PrefixProjectedLiftColorDirCore Cyl :=
  activePermutedColorDirCore Cyl A (activePrefixTailPerm hT) hCyl

noncomputable def activePrefixColorDirCoreDirectCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} (A : ActiveSymboling Cyl)
    (hT : 2 ≤ n + 1)
    (c : Fin (b + (n + 1))) (y : Shared.TorusVertex (b + 1) m)
    (z : Fin n → ZMod m) (τ : Fin n) : ZMod m :=
  activePermutedColorDirCoreDirectCarry A (activePrefixTailPerm hT) c y z τ

theorem activePrefixColorDirCoreDirectCarry_zero
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} (A : ActiveSymboling Cyl)
    (hT : 2 ≤ n + 1)
    (c : Fin (b + (n + 1))) (y : Shared.TorusVertex (b + 1) m)
    (z : Fin n → ZMod m) (h0 : 0 < n) :
    activePrefixColorDirCoreDirectCarry A hT c y z ⟨0, h0⟩ =
      if A.Φ.color y ⟨0, by omega⟩ = c then (1 : ZMod m) else 0 := by
  classical
  let zeroTail : Fin (n + 1) := ⟨0, by omega⟩
  change
    activePrefixColorDirCoreDirectCarry A hT c y z ⟨0, h0⟩ =
      if A.Φ.color y zeroTail = c then (1 : ZMod m) else 0
  by_cases hactive : Cyl.dir c y = activeDir b
  · let hmem : c ∈ Cyl.active y :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
    let p :
        {c : Fin (b + (n + 1)) // c ∈ (Cyl.incidence).active y} :=
      ⟨c, by
        change c ∈ Cyl.active y
        exact hmem⟩
    let s : Fin (n + 1) := (A.Φ.equiv y).symm p
    have hperm_iff :
        (activePrefixTailPerm hT y z s = (⟨0, h0⟩ : Fin n).castSucc) ↔
          s.val = 0 := by
      constructor
      · intro h
        have hval :
            (activeTailLambdaRho (n + 1)
              (activeTailCanonicalRho hT z) s).val = 0 := by
          simpa [activePrefixTailPerm_apply] using congrArg Fin.val h
        exact
          (activeTailLambdaRho_val_eq_zero_iff
            (activeTailCanonicalRho hT z)
            (activeTailCanonicalRho_ne_zero hT z)).mp hval
      · intro hs
        apply Fin.ext
        have hval :
            (activeTailLambdaRho (n + 1)
              (activeTailCanonicalRho hT z) s).val = 0 :=
          (activeTailLambdaRho_val_eq_zero_iff
            (activeTailCanonicalRho hT z)
            (activeTailCanonicalRho_ne_zero hT z)).mpr hs
        simpa [activePrefixTailPerm_apply] using hval
    have hcolor_iff :
        A.Φ.color y zeroTail = c ↔ s.val = 0 := by
      constructor
      · intro hcolor
        have hp : A.Φ.equiv y zeroTail = p := by
          apply Subtype.ext
          simpa [ActiveHall.Symboling.color, zeroTail, p] using hcolor
        have hs : s = zeroTail := by
          have hsymm := congrArg ((A.Φ.equiv y).symm) hp
          simpa [s] using hsymm.symm
        exact congrArg Fin.val hs
      · intro hsval
        have hs : s = zeroTail := Fin.ext hsval
        have hp : A.Φ.equiv y zeroTail = p := by
          rw [← hs]
          exact (A.Φ.equiv y).apply_symm_apply p
        exact congrArg Subtype.val hp
    by_cases hcolor : A.Φ.color y zeroTail = c
    · have hsval : s.val = 0 := hcolor_iff.mp hcolor
      have hperm := hperm_iff.mpr hsval
      have hperm0 :
          activeTailLambdaRho (n + 1) (activeTailCanonicalRho hT z)
              ((A.Φ.equiv y).symm p) =
            (0 : Fin (n + 1)) := by
        simpa [activePrefixTailPerm_apply, s] using hperm
      calc
        activePrefixColorDirCoreDirectCarry A hT c y z ⟨0, h0⟩ =
            (1 : ZMod m) := by
          simp [activePrefixColorDirCoreDirectCarry,
            activePermutedColorDirCoreDirectCarry, hactive, p, hperm0]
        _ = (if A.Φ.color y zeroTail = c then (1 : ZMod m) else 0) := by
          rw [if_pos hcolor]
    · have hsval : s.val ≠ 0 := by
        intro hs
        exact hcolor (hcolor_iff.mpr hs)
      have hperm : activePrefixTailPerm hT y z s ≠
          (⟨0, h0⟩ : Fin n).castSucc := by
        intro h
        exact hsval (hperm_iff.mp h)
      have hperm0 :
          activeTailLambdaRho (n + 1) (activeTailCanonicalRho hT z)
              ((A.Φ.equiv y).symm p) ≠
            (0 : Fin (n + 1)) := by
        intro h
        exact hperm (by
          simpa [activePrefixTailPerm_apply, s] using h)
      calc
        activePrefixColorDirCoreDirectCarry A hT c y z ⟨0, h0⟩ =
            (0 : ZMod m) := by
          simp [activePrefixColorDirCoreDirectCarry,
            activePermutedColorDirCoreDirectCarry, hactive, p, hperm0]
        _ = (if A.Φ.color y zeroTail = c then (1 : ZMod m) else 0) := by
          rw [if_neg hcolor]
  · have hcolor : A.Φ.color y zeroTail ≠ c := by
      intro hc
      have hmemColor :=
        ActiveHall.Symboling.color_mem_active A.Φ y zeroTail
      have hcActive' : c ∈ (Cyl.incidence).active y := by
        rw [← hc]
        exact hmemColor
      have hcActive : c ∈ Cyl.active y := by
        exact hcActive'
      exact hactive (Finset.mem_filter.mp hcActive).2
    calc
      activePrefixColorDirCoreDirectCarry A hT c y z ⟨0, h0⟩ =
          (0 : ZMod m) := by
        simp [activePrefixColorDirCoreDirectCarry,
          activePermutedColorDirCoreDirectCarry, hactive]
      _ = (if A.Φ.color y zeroTail = c then (1 : ZMod m) else 0) := by
        rw [if_neg hcolor]

theorem activePrefixPermutedColorDirCore_fiberStep_coord_eq_add_directCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1) (hCyl : IsCylinder Cyl)
    (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (τ : Fin n) :
    (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y z τ =
      z τ + activePrefixColorDirCoreDirectCarry A hT c y z τ := by
  exact
    activePermutedColorDirCore_fiberStep_coord_eq_add_directCarry
      (activePrefixTailPerm hT) hCyl c y z τ

theorem activePrefixPermutedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1) (hCyl : IsCylinder Cyl)
    (c : Fin (b + (n + 1)))
    (base : Shared.TorusVertex (b + 1) m) (period : Nat)
    (z : Fin n → ZMod m) (τ : Fin n) :
    Shared.sectionReturn
        (Shared.skewProductMap
          (Cyl.step c)
          ((activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c))
        base period z τ =
      z τ +
        ∑ u ∈ Finset.range period,
          activePrefixColorDirCoreDirectCarry A hT c
            (((Cyl.step c)^[u]) base)
            (Shared.skewFiberIterate
              (Cyl.step c)
              ((activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c)
              u base z)
            τ := by
  exact
    activePermutedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
      (activePrefixTailPerm hT) hCyl c base period z τ

/--
Lower-triangular monodromy form of the projected primitive lift.

For each color, the expanded step is conjugate to a skew product over the
cylinder color cycle.  The section return on the collapse fiber is required to
be a lower-triangular `ZMod` vector map with unit total carries, exactly the
shape consumed by `Shared.zmodVectorLowerTriangularUnitCycleCoordinate`.
-/
structure PrefixProjectedLowerTriangularLiftColorDir {b m n : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m (n + 1) packets) where
  core : PrefixProjectedLiftColorDirCore Cyl
  base : Fin (b + (n + 1)) → Shared.TorusVertex (b + 1) m
  period : Fin (b + (n + 1)) → Nat
  fiber_bijective :
    ∀ c : Fin (b + (n + 1)),
      ∀ y : Shared.TorusVertex (b + 1) m,
        Function.Bijective (core.fiberStep c y)
  return_base :
    ∀ c : Fin (b + (n + 1)),
      ((Cyl.step c)^[period c]) (base c) = base c
  base_cover :
    ∀ c : Fin (b + (n + 1)),
      ∀ y : Shared.TorusVertex (b + 1) m,
        ∃ k : Nat, k < period c ∧ ((Cyl.step c)^[k]) (base c) = y
  gamma :
    Fin (b + (n + 1)) →
      ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m
  return_lower_triangular :
    ∀ c : Fin (b + (n + 1)),
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        Shared.sectionReturn
            (Shared.skewProductMap (Cyl.step c) (core.fiberStep c))
            (base c) (period c) z ⟨k, hk⟩
          =
        z ⟨k, hk⟩ +
          gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z)
  return_unit :
    ∀ c : Fin (b + (n + 1)),
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), gamma c k hk z)

namespace PrefixProjectedLowerTriangularLiftColorDir

theorem colorHamiltonian {b m n : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m (n + 1) packets}
    (D : PrefixProjectedLowerTriangularLiftColorDir Cyl)
    (hCyl : IsCylinder Cyl) :
    Shared.IsCayleyColorHamiltonian D.core.colorDir := by
  intro c
  let F : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    Shared.sectionReturn
      (Shared.skewProductMap (Cyl.step c) (D.core.fiberStep c))
      (D.base c) (D.period c)
  have htri :
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        F z ⟨k, hk⟩ =
          z ⟨k, hk⟩ +
            D.gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z) := by
    intro z k hk
    exact D.return_lower_triangular c z k hk
  have hunit :
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), D.gamma c k hk z) := by
    intro k hk
    exact D.return_unit c k hk
  rcases
      Shared.zmodVectorLowerTriangularUnitCycleCoordinate
        (m := m) (r := n) F (D.gamma c) htri hunit
    with ⟨rank, hrank⟩
  have hmonodromy :
      Shared.IsSingleCycleMap F :=
    (Shared.CycleCoordinate.ofRankEquiv rank hrank).singleCycle
  have hskew :
      Shared.IsSingleCycleMap
        (Shared.skewProductMap (Cyl.step c) (D.core.fiberStep c)) :=
    Shared.single_cycle_of_skewProduct_base_orbit_monodromy
      (Cyl.step c) (D.core.fiberStep c)
      (D.base c) (D.period c)
      (hCyl.color_hamiltonian c).1
      (D.fiber_bijective c)
      (D.return_base c)
      (D.base_cover c)
      hmonodromy
  exact
    Shared.single_cycle_of_equiv_conj
      (collapseVertexFiberEquiv b m n).symm
      (Shared.cayleyColorStep D.core.colorDir c)
      (Shared.skewProductMap (Cyl.step c) (D.core.fiberStep c))
      hskew
      (fun p => by
        simpa using D.core.skew_conj c p)

noncomputable def toProjected {b m n : Nat} [NeZero m]
    {packets : List (List Nat)} {Cyl : Cylinder b m (n + 1) packets}
    (D : PrefixProjectedLowerTriangularLiftColorDir Cyl)
    (hCyl : IsCylinder Cyl) :
    PrefixProjectedLiftColorDir Cyl where
  colorDir := D.core.colorDir
  edgePartition := D.core.edgePartition
  colorHamiltonian := D.colorHamiltonian hCyl
  collapse_step := D.core.collapse_step

end PrefixProjectedLowerTriangularLiftColorDir

/--
Concrete primitive prefix-lift target.

This asks for an actual expanded Cayley direction selector whose steps project
to the compressed cylinder and whose color classes are Hamiltonian.  The
projection field is not needed to package the final decomposition, but it is
the useful invariant for the intended prefix-tail proof.
-/
def PrimitiveActivePrefixProjectedLiftAssemblyGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T),
      IsCylinder Cyl →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      Nonempty (PrefixProjectedLiftColorDir Cyl)

/--
Primitive prefix-lift target reduced to lower-triangular fiber monodromy.

This is the sharper residual expected by the prefix-tail proof: build a
projected expanded selector and prove its fiber section return has unit
lower-triangular carries.  The generic skew-product and triangular-cycle
machinery then supplies Hamiltonicity.
-/
def PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal : Prop :=
  ∀ {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1),
      IsCylinder Cyl →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      Nonempty (PrefixProjectedLowerTriangularLiftColorDir Cyl)

theorem primitiveActivePrefixProjectedLiftAssemblyGoal_of_lowerTriangular
    (hLift : PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal) :
    PrimitiveActivePrefixProjectedLiftAssemblyGoal := by
  intro b m T _inst packets Cyl A hT hCyl hA hPrim
  cases T with
  | zero =>
      omega
  | succ n =>
      rcases hLift (b := b) (m := m) (n := n)
          (packets := packets) (Cyl := Cyl) (A := A)
          hT hCyl hA hPrim with ⟨D⟩
      exact ⟨D.toProjected hCyl⟩

theorem primitiveActivePrefixLiftAssemblyGoal_of_projectedLift
    (hLift : PrimitiveActivePrefixProjectedLiftAssemblyGoal) :
    PrimitiveActivePrefixLiftAssemblyGoal := by
  intro b m T _inst packets Cyl A hT hCyl hA hPrim
  rcases hLift hT hCyl hA hPrim with ⟨D⟩
  exact ⟨{
    colorDir := D.colorDir
    edgePartition := D.edgePartition
    colorHamiltonian := D.colorHamiltonian
  }⟩

theorem primitiveActiveLiftAssemblyGoal_of_prefixLiftAssembly
    (hLift : PrimitiveActivePrefixLiftAssemblyGoal) :
    PrimitiveActiveLiftAssemblyGoal := by
  intro b m T _inst packets Cyl A hT hCyl hA
  exact hLift hT hCyl hA.1
    (activeSymbolingCountsPrimitive_of_isPrimitive hT hA)

abbrev ActiveTailPerm (b m n : Nat) :=
  Shared.TorusVertex (b + 1) m →
    (Fin n → ZMod m) → (Fin (n + 1) ≃ Fin (n + 1))

/--
Lower-triangular monodromy data for a fiber-dependent active-tail
permutation.

The data chooses the permutation rule itself.  This keeps the generic
Latin/projection skeleton separate from the final prefix-count `lambda_rho`
choice of permutation.
-/
structure ActivePermutedColorDirLowerTriangularMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets}
    (A : ActiveSymboling Cyl) (hCyl : IsCylinder Cyl) where
  tailPerm : ActiveTailPerm b m n
  fiber_bijective :
    ∀ c : Fin (b + (n + 1)),
      ∀ y : Shared.TorusVertex (b + 1) m,
        Function.Bijective
          ((activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y)
  base : Fin (b + (n + 1)) → Shared.TorusVertex (b + 1) m
  period : Fin (b + (n + 1)) → Nat
  return_base :
    ∀ c : Fin (b + (n + 1)),
      ((Cyl.step c)^[period c]) (base c) = base c
  base_cover :
    ∀ c : Fin (b + (n + 1)),
      ∀ y : Shared.TorusVertex (b + 1) m,
        ∃ k : Nat, k < period c ∧ ((Cyl.step c)^[k]) (base c) = y
  gamma :
    Fin (b + (n + 1)) →
      ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m
  return_lower_triangular :
    ∀ c : Fin (b + (n + 1)),
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        Shared.sectionReturn
            (Shared.skewProductMap
              (Cyl.step c)
              ((activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c))
            (base c) (period c) z ⟨k, hk⟩
          =
        z ⟨k, hk⟩ +
          gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z)
  return_unit :
    ∀ c : Fin (b + (n + 1)),
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), gamma c k hk z)

structure ActivePermutedColorDirFiberLowerTriangularMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets}
    (A : ActiveSymboling Cyl) (hCyl : IsCylinder Cyl)
    (B : CylinderBaseCycleData Cyl) where
  tailPerm : ActiveTailPerm b m n
  fiber_bijective :
    ∀ c : Fin (b + (n + 1)),
      ∀ y : Shared.TorusVertex (b + 1) m,
        Function.Bijective
          ((activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c y)
  gamma :
    Fin (b + (n + 1)) →
      ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m
  return_lower_triangular :
    ∀ c : Fin (b + (n + 1)),
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        Shared.sectionReturn
            (Shared.skewProductMap
              (Cyl.step c)
              ((activePermutedColorDirCore Cyl A tailPerm hCyl).fiberStep c))
            (B.base c) (B.period c) z ⟨k, hk⟩
          =
        z ⟨k, hk⟩ +
          gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z)
  return_unit :
    ∀ c : Fin (b + (n + 1)),
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), gamma c k hk z)

namespace ActivePermutedColorDirFiberLowerTriangularMonodromyData

def toMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    {hCyl : IsCylinder Cyl} {B : CylinderBaseCycleData Cyl}
    (D : ActivePermutedColorDirFiberLowerTriangularMonodromyData A hCyl B) :
    ActivePermutedColorDirLowerTriangularMonodromyData A hCyl where
  tailPerm := D.tailPerm
  fiber_bijective := D.fiber_bijective
  base := B.base
  period := B.period
  return_base := B.return_base
  base_cover := B.base_cover
  gamma := D.gamma
  return_lower_triangular := D.return_lower_triangular
  return_unit := D.return_unit

end ActivePermutedColorDirFiberLowerTriangularMonodromyData

namespace ActivePermutedColorDirLowerTriangularMonodromyData

noncomputable def toLowerTriangularLift
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    {hCyl : IsCylinder Cyl}
    (D : ActivePermutedColorDirLowerTriangularMonodromyData A hCyl) :
    PrefixProjectedLowerTriangularLiftColorDir Cyl where
  core := activePermutedColorDirCore Cyl A D.tailPerm hCyl
  base := D.base
  period := D.period
  fiber_bijective := D.fiber_bijective
  return_base := D.return_base
  base_cover := D.base_cover
  gamma := D.gamma
  return_lower_triangular := D.return_lower_triangular
  return_unit := D.return_unit

end ActivePermutedColorDirLowerTriangularMonodromyData

def ActivePermutedColorDirLowerTriangularMonodromyGoal : Prop :=
  ∀ {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1),
      (hCyl : IsCylinder Cyl) →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      Nonempty (ActivePermutedColorDirLowerTriangularMonodromyData A hCyl)

def ActivePermutedColorDirFiberLowerTriangularMonodromyGoal : Prop :=
  ∀ {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1),
      (hCyl : IsCylinder Cyl) →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      (B : CylinderBaseCycleData Cyl) →
      Nonempty
        (ActivePermutedColorDirFiberLowerTriangularMonodromyData A hCyl B)

theorem activePermutedColorDirLowerTriangularMonodromyGoal_of_baseCycle_fiber
    (hFiber : ActivePermutedColorDirFiberLowerTriangularMonodromyGoal) :
    ActivePermutedColorDirLowerTriangularMonodromyGoal := by
  intro b m n _inst packets Cyl A hT hCyl hA hPrim
  rcases cylinderBaseCycleData_of_isCylinder hCyl with ⟨B⟩
  rcases hFiber hT hCyl hA hPrim B with ⟨D⟩
  exact ⟨D.toMonodromyData⟩

theorem primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePermutedMonodromy
    (hMono : ActivePermutedColorDirLowerTriangularMonodromyGoal) :
    PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal := by
  intro b m n _inst packets Cyl A hT hCyl hA hPrim
  rcases hMono hT hCyl hA hPrim with ⟨D⟩
  exact ⟨D.toLowerTriangularLift⟩

theorem primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePermutedFiberMonodromy
    (hFiber : ActivePermutedColorDirFiberLowerTriangularMonodromyGoal) :
    PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal :=
  primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePermutedMonodromy
    (activePermutedColorDirLowerTriangularMonodromyGoal_of_baseCycle_fiber
      hFiber)

/--
Canonical active-prefix specialization of the active-permuted monodromy
residual.

This is the theorem surface for the concrete prefix-count `lambda_rho` tail
rule.  It removes the arbitrary `tailPerm` parameter from the generic
active-permuted residual.
-/
structure ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets}
    (A : ActiveSymboling Cyl) (hT : 2 ≤ n + 1)
    (hCyl : IsCylinder Cyl) (B : CylinderBaseCycleData Cyl) where
  fiber_bijective :
    ∀ c : Fin (b + (n + 1)),
      ∀ y : Shared.TorusVertex (b + 1) m,
        Function.Bijective
          ((activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y)
  gamma :
    Fin (b + (n + 1)) →
      ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m
  return_lower_triangular :
    ∀ c : Fin (b + (n + 1)),
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        Shared.sectionReturn
            (Shared.skewProductMap
              (Cyl.step c)
              ((activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c))
            (B.base c) (B.period c) z ⟨k, hk⟩
          =
        z ⟨k, hk⟩ +
          gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z)
  return_unit :
    ∀ c : Fin (b + (n + 1)),
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), gamma c k hk z)

namespace ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyData

noncomputable def toActivePermutedData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    {hT : 2 ≤ n + 1} {hCyl : IsCylinder Cyl}
    {B : CylinderBaseCycleData Cyl}
    (D :
      ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyData
        A hT hCyl B) :
    ActivePermutedColorDirFiberLowerTriangularMonodromyData A hCyl B where
  tailPerm := activePrefixTailPerm hT
  fiber_bijective := D.fiber_bijective
  gamma := D.gamma
  return_lower_triangular := D.return_lower_triangular
  return_unit := D.return_unit

end ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyData

def ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyGoal : Prop :=
  ∀ {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1),
      (hCyl : IsCylinder Cyl) →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      (B : CylinderBaseCycleData Cyl) →
      Nonempty
        (ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyData
          A hT hCyl B)

theorem activePermutedColorDirFiberLowerTriangularMonodromyGoal_of_activePrefix
    (hFiber : ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyGoal) :
    ActivePermutedColorDirFiberLowerTriangularMonodromyGoal := by
  intro b m n _inst packets Cyl A hT hCyl hA hPrim B
  rcases hFiber hT hCyl hA hPrim B with ⟨D⟩
  exact ⟨D.toActivePermutedData⟩

theorem primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePrefixPermutedFiberMonodromy
    (hFiber : ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyGoal) :
    PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal :=
  primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePermutedFiberMonodromy
    (activePermutedColorDirFiberLowerTriangularMonodromyGoal_of_activePrefix
      hFiber)

def ExpandedColorDirEdgePartitionGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl},
      IsCylinder Cyl →
      Shared.IsCayleyEdgePartition (expandedColorDir Cyl A)

def ExpandedColorDirColorHamiltonianGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ T),
      IsCylinder Cyl →
      IsPrimitiveActiveSymboling hT A →
      Shared.IsCayleyColorHamiltonian (expandedColorDir Cyl A)

theorem primitiveActiveLiftAssemblyGoal_of_expandedColorDirPieces
    (hEdge : ExpandedColorDirEdgePartitionGoal)
    (hHam : ExpandedColorDirColorHamiltonianGoal) :
    PrimitiveActiveLiftAssemblyGoal := by
  intro b m T _inst packets Cyl A hT hCyl hA
  exact ⟨{
    colorDir := expandedColorDir Cyl A
    edgePartition := hEdge hCyl
    colorHamiltonian := hHam hT hCyl hA
  }⟩

theorem primitiveActivePrefixProjectedLiftAssemblyGoal_of_expandedColorDirPieces
    (hEdge : ExpandedColorDirEdgePartitionGoal)
    (hHam : ExpandedColorDirColorHamiltonianGoal) :
    PrimitiveActivePrefixProjectedLiftAssemblyGoal := by
  intro b m T _inst packets Cyl A hT hCyl hA hPrim
  refine ⟨{
    colorDir := expandedColorDir Cyl A
    edgePartition := hEdge hCyl
    colorHamiltonian := hHam hT hCyl
      (isPrimitiveActiveSymboling_of_countsPrimitive hT hA hPrim)
    collapse_step := ?_
  }⟩
  intro c x
  exact collapseVertex_cayleyColorStep_expandedColorDir Cyl A c x

theorem expandedColorDirEdgePartitionGoal :
    ExpandedColorDirEdgePartitionGoal := by
  classical
  intro b m T _inst packets Cyl A hCyl x j
  let y := collapseVertex b m T x
  by_cases hj : j.val < b
  · let i : Fin (b + 1) := ordinaryBaseDirOfExpandedDir j hj
    have hi : i ≠ activeDir b :=
      ordinaryBaseDirOfExpandedDir_ne_active j hj
    rcases hCyl.ordinary_unique y i hi with ⟨c, hc, huniq⟩
    refine ⟨c, ?_, ?_⟩
    · have hnot : Cyl.dir c y ≠ activeDir b := by
        rw [hc]
        exact hi
      apply Fin.ext
      simp [expandedColorDir, y, hi, ordinaryExpandedDir, hc]
      rfl
    · intro d hd
      have hnot : Cyl.dir d y ≠ activeDir b := by
        intro hactive
        have hval := congrArg Fin.val hd
        have hge : b ≤ (expandedColorDir Cyl A d x).val := by
          simp [expandedColorDir, y, hactive, tailExpandedDir]
        rw [hval] at hge
        omega
      have hdir : Cyl.dir d y = i := by
        apply Fin.ext
        have hval := congrArg Fin.val hd
        have hval' :
            (expandedColorDir Cyl A d x).val = (Cyl.dir d y).val := by
          simp [expandedColorDir, y, hnot, ordinaryExpandedDir]
        rw [hval'] at hval
        simpa [i, ordinaryBaseDirOfExpandedDir] using hval
      exact huniq d hdir
  · have hjge : b ≤ j.val := by omega
    let σ : Fin T := tailSymbolOfExpandedDir j hjge
    let p : {c : Fin (b + T) // c ∈ (Cyl.incidence).active y} :=
      A.Φ.equiv y σ
    let c : Fin (b + T) := p.1
    have hcActive : Cyl.dir c y = activeDir b := by
      have hp : c ∈ Cyl.active y := by
        simp [Cylinder.incidence, c, p]
      exact (Finset.mem_filter.mp hp).2
    have hsub :
        (⟨c, by
          change c ∈ Cyl.active y
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcActive⟩⟩ :
          {c : Fin (b + T) // c ∈ (Cyl.incidence).active y}) = p := by
      apply Subtype.ext
      rfl
    have hsymm :
        (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcActive⟩⟩ :
            {c : Fin (b + T) // c ∈ (Cyl.incidence).active y}) = σ := by
      rw [hsub]
      exact (A.Φ.equiv y).symm_apply_apply σ
    refine ⟨c, ?_, ?_⟩
    · calc
        expandedColorDir Cyl A c x = tailExpandedDir b σ := by
          simp [expandedColorDir, y, hcActive, hsymm]
        _ = j := tailExpandedDir_of_tailSymbol j hjge
    · intro d hd
      have hactive : Cyl.dir d y = activeDir b := by
        by_contra hnot
        have hval := congrArg Fin.val hd
        have hlt : (expandedColorDir Cyl A d x).val < b := by
          simp [expandedColorDir, y, hnot, ordinaryExpandedDir_val_lt]
        rw [hval] at hlt
        omega
      have hdmem : d ∈ Cyl.active y :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ d, hactive⟩
      let q : {c : Fin (b + T) // c ∈ (Cyl.incidence).active y} :=
        ⟨d, by
          change d ∈ Cyl.active y
          exact hdmem⟩
      have hsymm_d : (A.Φ.equiv y).symm q = σ := by
        have hbranch :
            expandedColorDir Cyl A d x =
              tailExpandedDir b ((A.Φ.equiv y).symm q) := by
          simp [expandedColorDir, y, hactive, q]
        apply tailExpandedDir_injective (b := b)
        rw [← hbranch, hd]
        exact (tailExpandedDir_of_tailSymbol j hjge).symm
      have hq : q = p := by
        have happly := congrArg (A.Φ.equiv y) hsymm_d
        simpa [q, p] using happly
      exact congrArg Subtype.val hq

noncomputable def expandedColorDirCore {b m n : Nat} [NeZero m]
    {packets : List (List Nat)}
    (Cyl : Cylinder b m (n + 1) packets)
    (A : ActiveSymboling Cyl)
    (hCyl : IsCylinder Cyl) :
    PrefixProjectedLiftColorDirCore Cyl where
  colorDir := expandedColorDir Cyl A
  edgePartition := expandedColorDirEdgePartitionGoal hCyl
  collapse_step := by
    intro c x
    exact collapseVertex_cayleyColorStep_expandedColorDir Cyl A c x

theorem expandedColorDirCore_fiberStep_of_inactive
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (hdir : Cyl.dir c y ≠ activeDir b) :
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z = z := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hy :
      collapseVertex b m (n + 1) x = y := by
    have h :=
      congrArg Prod.fst
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hcolor :
      expandedColorDir Cyl A c x =
        ordinaryExpandedDir (Cyl.dir c y) hdir := by
    simp [expandedColorDir, x, hy, hdir]
  have hfiber :=
    congrArg Prod.snd
      (collapseVertexFiberEquiv_add_ordinaryExpandedDir
        (b := b) (m := m) (n := n) x (Cyl.dir c y) hdir)
  calc
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z
        =
      (collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (ordinaryExpandedDir (Cyl.dir c y) hdir))).2 := by
        simp [PrefixProjectedLiftColorDirCore.fiberStep,
          expandedColorDirCore, Shared.cayleyColorStep, x, hcolor]
    _ = collapseFiberInit b m n x := by
        simpa using hfiber
    _ = z := hz

theorem expandedColorDirCore_fiberStep_of_tail_castSucc
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (σ : Fin n)
    (hcolor :
      expandedColorDir Cyl A c
          ((collapseVertexFiberEquiv b m n).symm (y, z)) =
        tailExpandedDir b σ.castSucc) :
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z =
      fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0 := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hcolor' :
      expandedColorDir Cyl A c x = tailExpandedDir b σ.castSucc := by
    simpa [x] using hcolor
  have hfiber :=
    congrArg Prod.snd
      (collapseVertexFiberEquiv_add_tailExpandedDir_castSucc
        (b := b) (m := m) (n := n) x σ)
  calc
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z
        =
      (collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b σ.castSucc))).2 := by
        simp [PrefixProjectedLiftColorDirCore.fiberStep,
          expandedColorDirCore, Shared.cayleyColorStep, x, hcolor']
    _ =
      (fun τ : Fin n =>
        collapseFiberInit b m n x τ +
          if τ = σ then (1 : ZMod m) else 0) := by
        simpa using hfiber
    _ = (fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0) := by
        funext τ
        rw [hz]

theorem expandedColorDirCore_fiberStep_of_tail_last
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (hcolor :
      expandedColorDir Cyl A c
          ((collapseVertexFiberEquiv b m n).symm (y, z)) =
        tailExpandedDir b (Fin.last n)) :
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z = z := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hz :
      collapseFiberInit b m n x = z := by
    have h :=
      congrArg Prod.snd
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hcolor' :
      expandedColorDir Cyl A c x = tailExpandedDir b (Fin.last n) := by
    simpa [x] using hcolor
  have hfiber :=
    congrArg Prod.snd
      (collapseVertexFiberEquiv_add_tailExpandedDir_last
        (b := b) (m := m) (n := n) x)
  calc
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z
        =
      (collapseVertexFiberEquiv b m n
        (x + Shared.torusBasis (b + (n + 1)) m
          (tailExpandedDir b (Fin.last n)))).2 := by
        simp [PrefixProjectedLiftColorDirCore.fiberStep,
          expandedColorDirCore, Shared.cayleyColorStep, x, hcolor']
    _ = collapseFiberInit b m n x := by
        simpa using hfiber
    _ = z := hz

theorem expandedColorDirCore_fiberStep_of_active_castSucc
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (σ : Fin n)
    (hactive : Cyl.dir c y = activeDir b)
    (hsym :
      (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}) =
        σ.castSucc) :
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z =
      fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0 := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hy :
      collapseVertex b m (n + 1) x = y := by
    have h :=
      congrArg Prod.fst
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hactive_x :
      Cyl.dir c (collapseVertex b m (n + 1) x) = activeDir b := by
    simpa [hy] using hactive
  have hmem_x : c ∈ Cyl.active (collapseVertex b m (n + 1) x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive_x⟩
  have hmem_y : c ∈ Cyl.active y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
  have hsym_base :
      (A.Φ.equiv (collapseVertex b m (n + 1) x)).symm
          (⟨c, by
            change c ∈ Cyl.active (collapseVertex b m (n + 1) x)
            exact hmem_x⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active
                (collapseVertex b m (n + 1) x)}) =
        (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact hmem_y⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}) :=
    activeSymboling_symm_congr (A := A) hy hmem_x hmem_y
  have hcolor :
      expandedColorDir Cyl A c x = tailExpandedDir b σ.castSucc := by
    calc
      expandedColorDir Cyl A c x =
          tailExpandedDir b
            ((A.Φ.equiv (collapseVertex b m (n + 1) x)).symm
              (⟨c, by
                change c ∈ Cyl.active (collapseVertex b m (n + 1) x)
                exact hmem_x⟩ :
                {c : Fin (b + (n + 1)) //
                  c ∈ (Cyl.incidence).active
                    (collapseVertex b m (n + 1) x)})) := by
        simp [expandedColorDir, hactive_x]
      _ =
          tailExpandedDir b
            ((A.Φ.equiv y).symm
              (⟨c, by
                change c ∈ Cyl.active y
                exact hmem_y⟩ :
                {c : Fin (b + (n + 1)) //
                  c ∈ (Cyl.incidence).active y})) :=
        congrArg (tailExpandedDir b) hsym_base
      _ = tailExpandedDir b σ.castSucc := congrArg (tailExpandedDir b) hsym
  exact expandedColorDirCore_fiberStep_of_tail_castSucc
    hCyl c y z σ hcolor

theorem expandedColorDirCore_fiberStep_of_active_last
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (hactive : Cyl.dir c y = activeDir b)
    (hsym :
      (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}) =
        Fin.last n) :
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z = z := by
  classical
  let x := (collapseVertexFiberEquiv b m n).symm (y, z)
  have hy :
      collapseVertex b m (n + 1) x = y := by
    have h :=
      congrArg Prod.fst
        ((collapseVertexFiberEquiv b m n).right_inv (y, z))
    exact h
  have hactive_x :
      Cyl.dir c (collapseVertex b m (n + 1) x) = activeDir b := by
    simpa [hy] using hactive
  have hmem_x : c ∈ Cyl.active (collapseVertex b m (n + 1) x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive_x⟩
  have hmem_y : c ∈ Cyl.active y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
  have hsym_base :
      (A.Φ.equiv (collapseVertex b m (n + 1) x)).symm
          (⟨c, by
            change c ∈ Cyl.active (collapseVertex b m (n + 1) x)
            exact hmem_x⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active
                (collapseVertex b m (n + 1) x)}) =
        (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact hmem_y⟩ :
            {c : Fin (b + (n + 1)) //
              c ∈ (Cyl.incidence).active y}) :=
    activeSymboling_symm_congr (A := A) hy hmem_x hmem_y
  have hcolor :
      expandedColorDir Cyl A c x = tailExpandedDir b (Fin.last n) := by
    calc
      expandedColorDir Cyl A c x =
          tailExpandedDir b
            ((A.Φ.equiv (collapseVertex b m (n + 1) x)).symm
              (⟨c, by
                change c ∈ Cyl.active (collapseVertex b m (n + 1) x)
                exact hmem_x⟩ :
                {c : Fin (b + (n + 1)) //
                  c ∈ (Cyl.incidence).active
                    (collapseVertex b m (n + 1) x)})) := by
        simp [expandedColorDir, hactive_x]
      _ =
          tailExpandedDir b
            ((A.Φ.equiv y).symm
              (⟨c, by
                change c ∈ Cyl.active y
                exact hmem_y⟩ :
                {c : Fin (b + (n + 1)) //
                  c ∈ (Cyl.incidence).active y})) :=
        congrArg (tailExpandedDir b) hsym_base
      _ = tailExpandedDir b (Fin.last n) := congrArg (tailExpandedDir b) hsym
  exact expandedColorDirCore_fiberStep_of_tail_last hCyl c y z hcolor

theorem zmodVector_add_single_bijective {m n : Nat} (σ : Fin n) :
    Function.Bijective
      (fun z : Fin n → ZMod m =>
        fun τ : Fin n => z τ + if τ = σ then (1 : ZMod m) else 0) := by
  classical
  let F : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ => z τ + if τ = σ then (1 : ZMod m) else 0
  let G : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ => z τ - if τ = σ then (1 : ZMod m) else 0
  have hleft : Function.LeftInverse G F := by
    intro z
    funext τ
    simp [F, G, sub_eq_add_neg, add_assoc]
  have hright : Function.RightInverse G F := by
    intro z
    funext τ
    simp [F, G, sub_eq_add_neg, add_comm, add_left_comm]
  exact ⟨hleft.injective, hright.surjective⟩

theorem zmodVector_piecewise_add_single_id_bijective {m n : Nat}
    (P : (Fin n → ZMod m) → Prop) [DecidablePred P] (σ : Fin n)
    (hPadd :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ + if τ = σ then (1 : ZMod m) else 0) ↔ P z)
    (hPsub :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ - if τ = σ then (1 : ZMod m) else 0) ↔ P z) :
    Function.Bijective
      (fun z : Fin n → ZMod m =>
        fun τ : Fin n =>
          if P z then z τ + if τ = σ then (1 : ZMod m) else 0
          else z τ) := by
  classical
  let F : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if P z then z τ + if τ = σ then (1 : ZMod m) else 0
      else z τ
  let G : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if P z then z τ - if τ = σ then (1 : ZMod m) else 0
      else z τ
  have hleft : Function.LeftInverse G F := by
    intro z
    funext τ
    by_cases hz : P z
    · have hF : P (F z) := by
        have h := (hPadd z).mpr hz
        simpa [F, hz] using h
      have hFτ :
          F z τ = z τ + if τ = σ then (1 : ZMod m) else 0 := by
        simp [F, hz]
      calc
        G (F z) τ =
            F z τ - if τ = σ then (1 : ZMod m) else 0 := by
              simp [G, hF]
        _ = z τ := by
              rw [hFτ]
              by_cases hτ : τ = σ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
    · have hF : ¬ P (F z) := by
        simpa [F, hz] using hz
      calc
        G (F z) τ = F z τ := by
          simp [G, hF]
        _ = z τ := by
          simp [F, hz]
  have hright : Function.RightInverse G F := by
    intro z
    funext τ
    by_cases hz : P z
    · have hG : P (G z) := by
        have h := (hPsub z).mpr hz
        simpa [G, hz] using h
      have hGτ :
          G z τ = z τ - if τ = σ then (1 : ZMod m) else 0 := by
        simp [G, hz]
      calc
        F (G z) τ =
            G z τ + if τ = σ then (1 : ZMod m) else 0 := by
              simp [F, hG]
        _ = z τ := by
              rw [hGτ]
              by_cases hτ : τ = σ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
    · have hG : ¬ P (G z) := by
        simpa [G, hz] using hz
      calc
        F (G z) τ = G z τ := by
          simp [F, hG]
        _ = z τ := by
          simp [G, hz]
  exact ⟨hleft.injective, hright.surjective⟩

theorem zmodVector_piecewise_id_add_single_bijective {m n : Nat}
    (P : (Fin n → ZMod m) → Prop) [DecidablePred P] (σ : Fin n)
    (hPadd :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ + if τ = σ then (1 : ZMod m) else 0) ↔ P z)
    (hPsub :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ - if τ = σ then (1 : ZMod m) else 0) ↔ P z) :
    Function.Bijective
      (fun z : Fin n → ZMod m =>
        fun τ : Fin n =>
          if P z then z τ
          else z τ + if τ = σ then (1 : ZMod m) else 0) := by
  classical
  let F : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if P z then z τ
      else z τ + if τ = σ then (1 : ZMod m) else 0
  let G : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if P z then z τ
      else z τ - if τ = σ then (1 : ZMod m) else 0
  have hleft : Function.LeftInverse G F := by
    intro z
    funext τ
    by_cases hz : P z
    · have hF : P (F z) := by
        simpa [F, hz] using hz
      calc
        G (F z) τ = F z τ := by
          simp [G, hF]
        _ = z τ := by
          simp [F, hz]
    · have hF : ¬ P (F z) := by
        intro hp
        exact hz ((hPadd z).mp (by simpa [F, hz] using hp))
      have hFτ :
          F z τ = z τ + if τ = σ then (1 : ZMod m) else 0 := by
        simp [F, hz]
      calc
        G (F z) τ =
            F z τ - if τ = σ then (1 : ZMod m) else 0 := by
              simp [G, hF]
        _ = z τ := by
              rw [hFτ]
              by_cases hτ : τ = σ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
  have hright : Function.RightInverse G F := by
    intro z
    funext τ
    by_cases hz : P z
    · have hG : P (G z) := by
        simpa [G, hz] using hz
      calc
        F (G z) τ = G z τ := by
          simp [F, hG]
        _ = z τ := by
          simp [G, hz]
    · have hG : ¬ P (G z) := by
        intro hp
        exact hz ((hPsub z).mp (by simpa [G, hz] using hp))
      have hGτ :
          G z τ = z τ - if τ = σ then (1 : ZMod m) else 0 := by
        simp [G, hz]
      calc
        F (G z) τ =
            G z τ + if τ = σ then (1 : ZMod m) else 0 := by
              simp [F, hG]
        _ = z τ := by
              rw [hGτ]
              by_cases hτ : τ = σ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
  exact ⟨hleft.injective, hright.surjective⟩

theorem zmodVector_piecewise_add_single_add_single_bijective {m n : Nat}
    (P : (Fin n → ZMod m) → Prop) [DecidablePred P]
    (σ υ : Fin n)
    (hPaddσ :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ + if τ = σ then (1 : ZMod m) else 0) ↔ P z)
    (hPsubσ :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ - if τ = σ then (1 : ZMod m) else 0) ↔ P z)
    (hPaddυ :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ + if τ = υ then (1 : ZMod m) else 0) ↔ P z)
    (hPsubυ :
      ∀ z : Fin n → ZMod m,
        P (fun τ : Fin n =>
          z τ - if τ = υ then (1 : ZMod m) else 0) ↔ P z) :
    Function.Bijective
      (fun z : Fin n → ZMod m =>
        fun τ : Fin n =>
          if P z then z τ + if τ = σ then (1 : ZMod m) else 0
          else z τ + if τ = υ then (1 : ZMod m) else 0) := by
  classical
  let F : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if P z then z τ + if τ = σ then (1 : ZMod m) else 0
      else z τ + if τ = υ then (1 : ZMod m) else 0
  let G : (Fin n → ZMod m) → (Fin n → ZMod m) :=
    fun z τ =>
      if P z then z τ - if τ = σ then (1 : ZMod m) else 0
      else z τ - if τ = υ then (1 : ZMod m) else 0
  have hleft : Function.LeftInverse G F := by
    intro z
    funext τ
    by_cases hz : P z
    · have hF : P (F z) := by
        have h := (hPaddσ z).mpr hz
        simpa [F, hz] using h
      have hFτ :
          F z τ = z τ + if τ = σ then (1 : ZMod m) else 0 := by
        simp [F, hz]
      calc
        G (F z) τ =
            F z τ - if τ = σ then (1 : ZMod m) else 0 := by
              simp [G, hF]
        _ = z τ := by
              rw [hFτ]
              by_cases hτ : τ = σ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
    · have hF : ¬ P (F z) := by
        intro hp
        exact hz ((hPaddυ z).mp (by simpa [F, hz] using hp))
      have hFτ :
          F z τ = z τ + if τ = υ then (1 : ZMod m) else 0 := by
        simp [F, hz]
      calc
        G (F z) τ =
            F z τ - if τ = υ then (1 : ZMod m) else 0 := by
              simp [G, hF]
        _ = z τ := by
              rw [hFτ]
              by_cases hτ : τ = υ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
  have hright : Function.RightInverse G F := by
    intro z
    funext τ
    by_cases hz : P z
    · have hG : P (G z) := by
        have h := (hPsubσ z).mpr hz
        simpa [G, hz] using h
      have hGτ :
          G z τ = z τ - if τ = σ then (1 : ZMod m) else 0 := by
        simp [G, hz]
      calc
        F (G z) τ =
            G z τ + if τ = σ then (1 : ZMod m) else 0 := by
              simp [F, hG]
        _ = z τ := by
              rw [hGτ]
              by_cases hτ : τ = σ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
    · have hG : ¬ P (G z) := by
        intro hp
        exact hz ((hPsubυ z).mp (by simpa [G, hz] using hp))
      have hGτ :
          G z τ = z τ - if τ = υ then (1 : ZMod m) else 0 := by
        simp [G, hz]
      calc
        F (G z) τ =
            G z τ + if τ = υ then (1 : ZMod m) else 0 := by
              simp [F, hG]
        _ = z τ := by
              rw [hGτ]
              by_cases hτ : τ = υ <;>
                simp [hτ, sub_eq_add_neg, add_assoc]
  exact ⟨hleft.injective, hright.surjective⟩

theorem activePrefixPermutedColorDirCore_fiberStep_bijective
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1) (hCyl : IsCylinder Cyl)
    (c : Fin (b + (n + 1))) (y : Shared.TorusVertex (b + 1) m) :
    Function.Bijective
      ((activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y) := by
  classical
  by_cases hactive : Cyl.dir c y = activeDir b
  · let hmem : c ∈ Cyl.active y :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
    let s : Fin (n + 1) :=
      (A.Φ.equiv y).symm
        (⟨c, by
          change c ∈ Cyl.active y
          exact hmem⟩ :
          {c : Fin (b + (n + 1)) //
            c ∈ (Cyl.incidence).active y})
    by_cases hs0 : s.val = 0
    · have hnpos : 0 < n := by omega
      let σ : Fin n := ⟨0, hnpos⟩
      have hstep :
          (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y =
            (fun z : Fin n → ZMod m =>
              fun τ : Fin n =>
                z τ + if τ = σ then (1 : ZMod m) else 0) := by
        funext z
        have hsym :
            (activePrefixTailPerm hT y z) s = σ.castSucc := by
          apply Fin.ext
          simp [activePrefixTailPerm_apply, activeTailLambdaRho, hs0, σ]
        exact
          activePermutedColorDirCore_fiberStep_of_active_castSucc
            (activePrefixTailPerm hT) hCyl c y z σ hactive
            (by simpa [s] using hsym)
      rw [hstep]
      exact zmodVector_add_single_bijective σ
    · by_cases hs1 : s.val = 1
      · have hstep :
            (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y =
              (fun z : Fin n → ZMod m =>
                fun τ : Fin n =>
                  if hρ : (activeTailCanonicalRho hT z).val < n then
                    z τ +
                      if τ = ⟨(activeTailCanonicalRho hT z).val, hρ⟩
                      then (1 : ZMod m) else 0
                  else z τ) := by
          funext z
          by_cases hρ : (activeTailCanonicalRho hT z).val < n
          · let σ : Fin n := ⟨(activeTailCanonicalRho hT z).val, hρ⟩
            have hsym :
                (activePrefixTailPerm hT y z) s = σ.castSucc := by
              apply Fin.ext
              simp [activePrefixTailPerm_apply, activeTailLambdaRho, hs1, σ]
            have h :=
              activePermutedColorDirCore_fiberStep_of_active_castSucc
                (activePrefixTailPerm hT) hCyl c y z σ hactive
                (by simpa [s] using hsym)
            funext τ
            have hτ := congrFun h τ
            simpa [hρ, σ] using hτ
          · have hρval : (activeTailCanonicalRho hT z).val = n := by
              have hle : (activeTailCanonicalRho hT z).val ≤ n :=
                Nat.le_of_lt_succ (activeTailCanonicalRho hT z).isLt
              omega
            have hsym :
                (activePrefixTailPerm hT y z) s = Fin.last n := by
              apply Fin.ext
              simp [activePrefixTailPerm_apply, activeTailLambdaRho, hs1,
                Fin.last, hρval]
            have h :=
              activePermutedColorDirCore_fiberStep_of_active_last
                (activePrefixTailPerm hT) hCyl c y z hactive
                (by simpa [s] using hsym)
            funext τ
            have hτ := congrFun h τ
            simpa [hρ] using hτ
        rw [hstep]
        exact activeTailCanonicalRho_dynamic_add_bijective hT
      · by_cases hslt : s.val < n
        · let σ : Fin n := ⟨s.val, hslt⟩
          let υ : Fin n := ⟨s.val - 1, by omega⟩
          let P : (Fin n → ZMod m) → Prop :=
            fun z => (activeTailCanonicalRho hT z).val < s.val
          have hstep :
              (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y =
                (fun z : Fin n → ZMod m =>
                  fun τ : Fin n =>
                    if P z then
                      z τ + if τ = σ then (1 : ZMod m) else 0
                    else
                      z τ + if τ = υ then (1 : ZMod m) else 0) := by
            funext z
            by_cases hP : P z
            · have hsym :
                  (activePrefixTailPerm hT y z) s = σ.castSucc := by
                apply Fin.ext
                have hlt :
                    (activeTailCanonicalRho hT z).val < s.val := by
                  simpa [P] using hP
                simp [activePrefixTailPerm_apply, activeTailLambdaRho,
                  hs0, hs1, hlt, σ]
              have h :=
                activePermutedColorDirCore_fiberStep_of_active_castSucc
                  (activePrefixTailPerm hT) hCyl c y z σ hactive
                  (by simpa [s] using hsym)
              funext τ
              have hτ := congrFun h τ
              calc
                (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y z τ =
                    z τ + if τ = σ then (1 : ZMod m) else 0 := by
                      simpa [activePrefixPermutedColorDirCore] using hτ
                _ =
                    (if P z then
                      z τ + if τ = σ then (1 : ZMod m) else 0
                    else
                      z τ + if τ = υ then (1 : ZMod m) else 0) := by
                      rw [if_pos hP]
            · have hsym :
                  (activePrefixTailPerm hT y z) s = υ.castSucc := by
                apply Fin.ext
                have hnotlt :
                    ¬ (activeTailCanonicalRho hT z).val < s.val := by
                  simpa [P] using hP
                simp [activePrefixTailPerm_apply, activeTailLambdaRho,
                  hs0, hs1, hnotlt, υ]
              have h :=
                activePermutedColorDirCore_fiberStep_of_active_castSucc
                  (activePrefixTailPerm hT) hCyl c y z υ hactive
                  (by simpa [s] using hsym)
              funext τ
              have hτ := congrFun h τ
              calc
                (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y z τ =
                    z τ + if τ = υ then (1 : ZMod m) else 0 := by
                      simpa [activePrefixPermutedColorDirCore] using hτ
                _ =
                    (if P z then
                      z τ + if τ = σ then (1 : ZMod m) else 0
                    else
                      z τ + if τ = υ then (1 : ZMod m) else 0) := by
                      rw [if_neg hP]
          rw [hstep]
          refine
            zmodVector_piecewise_add_single_add_single_bijective
              P σ υ ?_ ?_ ?_ ?_
          · intro z
            exact
              activeTailCanonicalRho_val_lt_add_single_iff
                hT (z := z) (q := s.val) (by omega)
                (σ := σ) (by
                  show s.val ≤ σ.val + 1
                  dsimp [σ]
                  omega)
          · intro z
            exact
              activeTailCanonicalRho_val_lt_sub_single_iff
                hT (z := z) (q := s.val) (by omega)
                (σ := σ) (by
                  show s.val ≤ σ.val + 1
                  dsimp [σ]
                  omega)
          · intro z
            exact
              activeTailCanonicalRho_val_lt_add_single_iff
                hT (z := z) (q := s.val) (by omega)
                (σ := υ) (by
                  show s.val ≤ υ.val + 1
                  simp [υ]
                  omega)
          · intro z
            exact
              activeTailCanonicalRho_val_lt_sub_single_iff
                hT (z := z) (q := s.val) (by omega)
                (σ := υ) (by
                  show s.val ≤ υ.val + 1
                  simp [υ]
                  omega)
        · have hsLast : s.val = n := by
            have hsle : s.val ≤ n := Nat.le_of_lt_succ s.isLt
            omega
          have hn0 : n ≠ 0 := by omega
          have hn1 : n ≠ 1 := by omega
          let υ : Fin n := ⟨n - 1, by omega⟩
          let P : (Fin n → ZMod m) → Prop :=
            fun z => (activeTailCanonicalRho hT z).val < n
          have hstep :
              (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y =
                (fun z : Fin n → ZMod m =>
                  fun τ : Fin n =>
                    if P z then z τ
                    else z τ + if τ = υ then (1 : ZMod m) else 0) := by
            funext z
            by_cases hP : P z
            · have hsym :
                  (activePrefixTailPerm hT y z) s = Fin.last n := by
                apply Fin.ext
                simp [activePrefixTailPerm_apply, activeTailLambdaRho,
                  P, hP, hsLast, hn0, hn1, Fin.last]
              have h :=
                activePermutedColorDirCore_fiberStep_of_active_last
                  (activePrefixTailPerm hT) hCyl c y z hactive
                  (by simpa [s] using hsym)
              funext τ
              have hτ := congrFun h τ
              simpa [P, hP] using hτ
            · have hρval : (activeTailCanonicalRho hT z).val = n := by
                have hle : (activeTailCanonicalRho hT z).val ≤ n :=
                  Nat.le_of_lt_succ (activeTailCanonicalRho hT z).isLt
                omega
              have hsym :
                  (activePrefixTailPerm hT y z) s = υ.castSucc := by
                apply Fin.ext
                simp [activePrefixTailPerm_apply, activeTailLambdaRho,
                  hρval, hsLast, hn0, hn1, υ]
              have h :=
                activePermutedColorDirCore_fiberStep_of_active_castSucc
                  (activePrefixTailPerm hT) hCyl c y z υ hactive
                  (by simpa [s] using hsym)
              funext τ
              have hτ := congrFun h τ
              simpa [P, hP, υ] using hτ
          rw [hstep]
          refine zmodVector_piecewise_id_add_single_bijective P υ ?_ ?_
          · intro z
            exact
              activeTailCanonicalRho_val_lt_add_single_iff
                hT (z := z) (q := n) (by omega)
                (σ := υ) (by
                  show n ≤ υ.val + 1
                  simp [υ]
                  omega)
          · intro z
            exact
              activeTailCanonicalRho_val_lt_sub_single_iff
                hT (z := z) (q := n) (by omega)
                (σ := υ) (by
                  show n ≤ υ.val + 1
                  simp [υ]
                  omega)
  · have hstep :
        (activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c y =
          id := by
      funext z
      exact
        activePermutedColorDirCore_fiberStep_of_inactive
          (activePrefixTailPerm hT) hCyl c y z hactive
    rw [hstep]
    exact Function.bijective_id

/--
Canonical active-prefix monodromy residual after local fiber invertibility has
been closed.

The remaining data is the lower-triangular section-return formula and unit carry
sum over the fixed cylinder base cycle.  One-step fiber bijectivity is supplied
by `activePrefixPermutedColorDirCore_fiberStep_bijective`.
-/
structure ActivePrefixPermutedColorDirFiberLowerTriangularReturnData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets}
    (A : ActiveSymboling Cyl) (hT : 2 ≤ n + 1)
    (hCyl : IsCylinder Cyl) (B : CylinderBaseCycleData Cyl) where
  gamma :
    Fin (b + (n + 1)) →
      ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m
  return_lower_triangular :
    ∀ c : Fin (b + (n + 1)),
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        Shared.sectionReturn
            (Shared.skewProductMap
              (Cyl.step c)
              ((activePrefixPermutedColorDirCore Cyl A hT hCyl).fiberStep c))
            (B.base c) (B.period c) z ⟨k, hk⟩
          =
        z ⟨k, hk⟩ +
          gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z)
  return_unit :
    ∀ c : Fin (b + (n + 1)),
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), gamma c k hk z)

namespace ActivePrefixPermutedColorDirFiberLowerTriangularReturnData

def toMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    {hT : 2 ≤ n + 1} {hCyl : IsCylinder Cyl}
    {B : CylinderBaseCycleData Cyl}
    (D :
      ActivePrefixPermutedColorDirFiberLowerTriangularReturnData
        A hT hCyl B) :
    ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyData
      A hT hCyl B where
  fiber_bijective :=
    activePrefixPermutedColorDirCore_fiberStep_bijective hT hCyl
  gamma := D.gamma
  return_lower_triangular := D.return_lower_triangular
  return_unit := D.return_unit

end ActivePrefixPermutedColorDirFiberLowerTriangularReturnData

def ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal : Prop :=
  ∀ {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1),
      (hCyl : IsCylinder Cyl) →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      (B : CylinderBaseCycleData Cyl) →
      Nonempty
        (ActivePrefixPermutedColorDirFiberLowerTriangularReturnData
          A hT hCyl B)

theorem activePrefixPermutedColorDirFiberLowerTriangularMonodromyGoal_of_return
    (hReturn : ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    ActivePrefixPermutedColorDirFiberLowerTriangularMonodromyGoal := by
  intro b m n _inst packets Cyl A hT hCyl hA hPrim B
  rcases hReturn hT hCyl hA hPrim B with ⟨D⟩
  exact ⟨D.toMonodromyData⟩

theorem primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePrefixPermutedFiberReturn
    (hReturn : ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal :=
  primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePrefixPermutedFiberMonodromy
    (activePrefixPermutedColorDirFiberLowerTriangularMonodromyGoal_of_return
      hReturn)

theorem expandedColorDirCore_fiberStep_bijective
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) :
    Function.Bijective ((expandedColorDirCore Cyl A hCyl).fiberStep c y) := by
  classical
  by_cases hactive : Cyl.dir c y = activeDir b
  · let hmem : c ∈ Cyl.active y :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
    let σfull : Fin (n + 1) :=
      (A.Φ.equiv y).symm
        (⟨c, by
          change c ∈ Cyl.active y
          exact hmem⟩ :
          {c : Fin (b + (n + 1)) // c ∈ (Cyl.incidence).active y})
    rcases Fin.eq_castSucc_or_eq_last σfull with ⟨σ, hσ⟩ | hlast
    · have hstep :
          (expandedColorDirCore Cyl A hCyl).fiberStep c y =
            fun z : Fin n → ZMod m =>
              fun τ : Fin n =>
                z τ + if τ = σ then (1 : ZMod m) else 0 := by
        funext z τ
        have hsym :
            (A.Φ.equiv y).symm
                (⟨c, by
                  change c ∈ Cyl.active y
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_univ c, hactive⟩⟩ :
                  {c : Fin (b + (n + 1)) //
                    c ∈ (Cyl.incidence).active y}) =
              σ.castSucc := by
          simpa [σfull, hmem] using hσ
        have h :=
          expandedColorDirCore_fiberStep_of_active_castSucc
            hCyl c y z σ hactive hsym
        exact congrFun h τ
      rw [hstep]
      exact zmodVector_add_single_bijective σ
    · have hstep :
          (expandedColorDirCore Cyl A hCyl).fiberStep c y =
            id := by
        funext z
        have hsym :
            (A.Φ.equiv y).symm
                (⟨c, by
                  change c ∈ Cyl.active y
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_univ c, hactive⟩⟩ :
                  {c : Fin (b + (n + 1)) //
                    c ∈ (Cyl.incidence).active y}) =
              Fin.last n := by
          simpa [σfull, hmem] using hlast
        exact expandedColorDirCore_fiberStep_of_active_last
          hCyl c y z hactive hsym
      rw [hstep]
      exact Function.bijective_id
  · have hstep :
        (expandedColorDirCore Cyl A hCyl).fiberStep c y =
          id := by
      funext z
      exact expandedColorDirCore_fiberStep_of_inactive hCyl c y z hactive
    rw [hstep]
    exact Function.bijective_id

noncomputable def expandedColorDirCoreDirectCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} (A : ActiveSymboling Cyl)
    (c : Fin (b + (n + 1))) (y : Shared.TorusVertex (b + 1) m)
    (τ : Fin n) : ZMod m :=
  if hactive : Cyl.dir c y = activeDir b then
    if
      (A.Φ.equiv y).symm
          (⟨c, by
            change c ∈ Cyl.active y
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩⟩ :
            {c : Fin (b + (n + 1)) // c ∈ (Cyl.incidence).active y}) =
        τ.castSucc
    then 1
    else 0
  else 0

theorem expandedColorDirCore_fiberStep_coord_eq_add_directCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (y : Shared.TorusVertex (b + 1) m) (z : Fin n → ZMod m)
    (τ : Fin n) :
    (expandedColorDirCore Cyl A hCyl).fiberStep c y z τ =
      z τ + expandedColorDirCoreDirectCarry A c y τ := by
  classical
  by_cases hactive : Cyl.dir c y = activeDir b
  · let hmem : c ∈ Cyl.active y :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, hactive⟩
    let σfull : Fin (n + 1) :=
      (A.Φ.equiv y).symm
        (⟨c, by
          change c ∈ Cyl.active y
          exact hmem⟩ :
          {c : Fin (b + (n + 1)) // c ∈ (Cyl.incidence).active y})
    by_cases hτσ : σfull = τ.castSucc
    · have hsym :
          (A.Φ.equiv y).symm
              (⟨c, by
                change c ∈ Cyl.active y
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_univ c, hactive⟩⟩ :
                {c : Fin (b + (n + 1)) //
                  c ∈ (Cyl.incidence).active y}) =
            τ.castSucc := by
        simpa [σfull, hmem] using hτσ
      have hstep :=
        expandedColorDirCore_fiberStep_of_active_castSucc
          hCyl c y z τ hactive hsym
      calc
        (expandedColorDirCore Cyl A hCyl).fiberStep c y z τ
            =
          (fun υ : Fin n =>
            z υ + if υ = τ then (1 : ZMod m) else 0) τ := by
            exact congrFun hstep τ
        _ = z τ + expandedColorDirCoreDirectCarry A c y τ := by
            simp [expandedColorDirCoreDirectCarry, hactive, hsym]
    · rcases Fin.eq_castSucc_or_eq_last σfull with ⟨σ, hσ⟩ | hlast
      · have hsym :
            (A.Φ.equiv y).symm
                (⟨c, by
                  change c ∈ Cyl.active y
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_univ c, hactive⟩⟩ :
                  {c : Fin (b + (n + 1)) //
                    c ∈ (Cyl.incidence).active y}) =
              σ.castSucc := by
          simpa [σfull, hmem] using hσ
        have hne : τ ≠ σ := by
          intro h
          apply hτσ
          rw [h, hσ]
        have hne' : σ ≠ τ := hne.symm
        have hstep :=
          expandedColorDirCore_fiberStep_of_active_castSucc
            hCyl c y z σ hactive hsym
        calc
          (expandedColorDirCore Cyl A hCyl).fiberStep c y z τ
              =
            (fun υ : Fin n =>
              z υ + if υ = σ then (1 : ZMod m) else 0) τ := by
              exact congrFun hstep τ
          _ = z τ + expandedColorDirCoreDirectCarry A c y τ := by
              simp [expandedColorDirCoreDirectCarry, hactive, hsym, hne,
                hne']
      · have hsym :
            (A.Φ.equiv y).symm
                (⟨c, by
                  change c ∈ Cyl.active y
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_univ c, hactive⟩⟩ :
                  {c : Fin (b + (n + 1)) //
                    c ∈ (Cyl.incidence).active y}) =
              Fin.last n := by
          simpa [σfull, hmem] using hlast
        have hlast_ne : (Fin.last n : Fin (n + 1)) ≠ τ.castSucc := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        have hstep :=
          expandedColorDirCore_fiberStep_of_active_last
            hCyl c y z hactive hsym
        calc
          (expandedColorDirCore Cyl A hCyl).fiberStep c y z τ = z τ := by
            exact congrFun hstep τ
          _ = z τ + expandedColorDirCoreDirectCarry A c y τ := by
            simp [expandedColorDirCoreDirectCarry, hactive, hsym, hlast_ne]
  · have hstep :=
      expandedColorDirCore_fiberStep_of_inactive (A := A) hCyl c y z hactive
    calc
      (expandedColorDirCore Cyl A hCyl).fiberStep c y z τ = z τ := by
        exact congrFun hstep τ
      _ = z τ + expandedColorDirCoreDirectCarry A c y τ := by
        simp [expandedColorDirCoreDirectCarry, hactive]

theorem expandedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (base : Shared.TorusVertex (b + 1) m) (period : Nat)
    (z : Fin n → ZMod m) (τ : Fin n) :
    Shared.sectionReturn
        (Shared.skewProductMap
          (Cyl.step c) ((expandedColorDirCore Cyl A hCyl).fiberStep c))
        base period z τ =
      z τ +
        ∑ u ∈ Finset.range period,
          expandedColorDirCoreDirectCarry A c
            (((Cyl.step c)^[u]) base) τ := by
  classical
  rw [Shared.sectionReturn_skewProductMap_eq_fiberIterate]
  exact
    Shared.skewFiberIterate_coord_eq_add_sum_range
      (Cyl.step c) ((expandedColorDirCore Cyl A hCyl).fiberStep c)
      (fun y _fiber => expandedColorDirCoreDirectCarry A c y τ)
      τ
      (by
        intro y fiber
        exact expandedColorDirCore_fiberStep_coord_eq_add_directCarry
          hCyl c y fiber τ)
      period base z

theorem expandedColorDirCore_sectionReturn_increment_eq_sum_directCarry
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (base : Shared.TorusVertex (b + 1) m) (period : Nat)
    (z : Fin n → ZMod m) (τ : Fin n) :
    Shared.sectionReturn
        (Shared.skewProductMap
          (Cyl.step c) ((expandedColorDirCore Cyl A hCyl).fiberStep c))
        base period z τ -
      z τ =
        ∑ u ∈ Finset.range period,
          expandedColorDirCoreDirectCarry A c
            (((Cyl.step c)^[u]) base) τ := by
  rw [expandedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
    hCyl c base period z τ]
  abel

theorem expandedColorDirCore_sectionReturn_increment_independent_of_fiber
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hCyl : IsCylinder Cyl) (c : Fin (b + (n + 1)))
    (base : Shared.TorusVertex (b + 1) m) (period : Nat)
    (z z' : Fin n → ZMod m) (τ : Fin n) :
    Shared.sectionReturn
        (Shared.skewProductMap
          (Cyl.step c) ((expandedColorDirCore Cyl A hCyl).fiberStep c))
        base period z τ -
      z τ =
    Shared.sectionReturn
        (Shared.skewProductMap
          (Cyl.step c) ((expandedColorDirCore Cyl A hCyl).fiberStep c))
        base period z' τ -
      z' τ := by
  rw [expandedColorDirCore_sectionReturn_increment_eq_sum_directCarry
      hCyl c base period z τ,
    expandedColorDirCore_sectionReturn_increment_eq_sum_directCarry
      hCyl c base period z' τ]

/--
The concrete monodromy data still needed for the intended expanded
base-tail lift.

The projected core, edge partition, and collapse compatibility are fixed to
`expandedColorDir`.  Thus this residual contains only the base orbit data and
the lower-triangular unit section-return proof for the fiber.
-/
structure ExpandedColorDirLowerTriangularMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets}
    (A : ActiveSymboling Cyl) (hCyl : IsCylinder Cyl) where
  base : Fin (b + (n + 1)) → Shared.TorusVertex (b + 1) m
  period : Fin (b + (n + 1)) → Nat
  return_base :
    ∀ c : Fin (b + (n + 1)),
      ((Cyl.step c)^[period c]) (base c) = base c
  base_cover :
    ∀ c : Fin (b + (n + 1)),
      ∀ y : Shared.TorusVertex (b + 1) m,
        ∃ k : Nat, k < period c ∧ ((Cyl.step c)^[k]) (base c) = y
  gamma :
    Fin (b + (n + 1)) →
      ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m
  return_lower_triangular :
    ∀ c : Fin (b + (n + 1)),
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        Shared.sectionReturn
            (Shared.skewProductMap
              (Cyl.step c) ((expandedColorDirCore Cyl A hCyl).fiberStep c))
            (base c) (period c) z ⟨k, hk⟩
          =
        z ⟨k, hk⟩ +
          gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z)
  return_unit :
    ∀ c : Fin (b + (n + 1)),
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), gamma c k hk z)

structure ExpandedColorDirFiberLowerTriangularMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets}
    (A : ActiveSymboling Cyl) (hCyl : IsCylinder Cyl)
    (B : CylinderBaseCycleData Cyl) where
  gamma :
    Fin (b + (n + 1)) →
      ∀ k : Nat, k < n → (Fin k → ZMod m) → ZMod m
  return_lower_triangular :
    ∀ c : Fin (b + (n + 1)),
      ∀ z : Fin n → ZMod m, ∀ k : Nat, ∀ hk : k < n,
        Shared.sectionReturn
            (Shared.skewProductMap
              (Cyl.step c) ((expandedColorDirCore Cyl A hCyl).fiberStep c))
            (B.base c) (B.period c) z ⟨k, hk⟩
          =
        z ⟨k, hk⟩ +
          gamma c k hk (Shared.zmodVectorTake (Nat.le_of_lt hk) z)
  return_unit :
    ∀ c : Fin (b + (n + 1)),
      ∀ k : Nat, ∀ hk : k < n,
        IsUnit (∑ z : (Fin k → ZMod m), gamma c k hk z)

namespace ExpandedColorDirFiberLowerTriangularMonodromyData

def toMonodromyData
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    {hCyl : IsCylinder Cyl} {B : CylinderBaseCycleData Cyl}
    (D : ExpandedColorDirFiberLowerTriangularMonodromyData A hCyl B) :
    ExpandedColorDirLowerTriangularMonodromyData A hCyl where
  base := B.base
  period := B.period
  return_base := B.return_base
  base_cover := B.base_cover
  gamma := D.gamma
  return_lower_triangular := D.return_lower_triangular
  return_unit := D.return_unit

end ExpandedColorDirFiberLowerTriangularMonodromyData

namespace ExpandedColorDirLowerTriangularMonodromyData

noncomputable def toLowerTriangularLift
    {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    {hCyl : IsCylinder Cyl}
    (D : ExpandedColorDirLowerTriangularMonodromyData A hCyl) :
    PrefixProjectedLowerTriangularLiftColorDir Cyl where
  core := expandedColorDirCore Cyl A hCyl
  base := D.base
  period := D.period
  fiber_bijective := expandedColorDirCore_fiberStep_bijective hCyl
  return_base := D.return_base
  base_cover := D.base_cover
  gamma := D.gamma
  return_lower_triangular := D.return_lower_triangular
  return_unit := D.return_unit

end ExpandedColorDirLowerTriangularMonodromyData

def PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal : Prop :=
  ∀ {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1),
      (hCyl : IsCylinder Cyl) →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      Nonempty (ExpandedColorDirLowerTriangularMonodromyData A hCyl)

def ExpandedColorDirFiberLowerTriangularMonodromyGoal : Prop :=
  ∀ {b m n : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m (n + 1) packets} {A : ActiveSymboling Cyl}
    (hT : 2 ≤ n + 1),
      (hCyl : IsCylinder Cyl) →
      IsActiveSymboling A →
      ActiveSymbolingCountsPrimitive hT A →
      (B : CylinderBaseCycleData Cyl) →
      Nonempty (ExpandedColorDirFiberLowerTriangularMonodromyData A hCyl B)

/--
Pointwise theorem surface for constructing expanded lower-triangular monodromy
from primitive active-symboling counts.  This is the implementation-facing name
below `PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal`.
-/
def ExpandedColorDirLowerTriangularMonodromyDataOfCountsPrimitiveGoal : Prop :=
  PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal

theorem primitiveActivePrefixExpandedLowerTriangularMonodromyGoal_of_baseCycle_fiber
    (hFiber : ExpandedColorDirFiberLowerTriangularMonodromyGoal) :
    PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal := by
  intro b m n _inst packets Cyl A hT hCyl hA hPrim
  rcases cylinderBaseCycleData_of_isCylinder hCyl with ⟨B⟩
  rcases hFiber hT hCyl hA hPrim B with ⟨D⟩
  exact ⟨D.toMonodromyData⟩

theorem primitiveActivePrefixExpandedLowerTriangularMonodromyGoal_of_countsPrimitiveData
    (hData : ExpandedColorDirLowerTriangularMonodromyDataOfCountsPrimitiveGoal) :
    PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal :=
  hData

theorem primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_expandedMonodromy
    (hMono : PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal) :
    PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal := by
  intro b m n _inst packets Cyl A hT hCyl hA hPrim
  rcases hMono hT hCyl hA hPrim with ⟨D⟩
  exact ⟨D.toLowerTriangularLift⟩

theorem primitiveActivePrefixLiftAssemblyGoal_of_expandedMonodromy
    (hMono : PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal) :
    PrimitiveActivePrefixLiftAssemblyGoal :=
  primitiveActivePrefixLiftAssemblyGoal_of_projectedLift
    (primitiveActivePrefixProjectedLiftAssemblyGoal_of_lowerTriangular
      (primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_expandedMonodromy
        hMono))

theorem primitiveActiveLiftAssemblyGoal_of_expandedColorDirHamiltonian
    (hHam : ExpandedColorDirColorHamiltonianGoal) :
    PrimitiveActiveLiftAssemblyGoal :=
  primitiveActiveLiftAssemblyGoal_of_expandedColorDirPieces
    expandedColorDirEdgePartitionGoal hHam

theorem primitiveActivePrefixProjectedLiftAssemblyGoal_of_expandedColorDirHamiltonian
    (hHam : ExpandedColorDirColorHamiltonianGoal) :
    PrimitiveActivePrefixProjectedLiftAssemblyGoal :=
  primitiveActivePrefixProjectedLiftAssemblyGoal_of_expandedColorDirPieces
    expandedColorDirEdgePartitionGoal hHam

theorem primitiveActivePrefixLiftAssemblyGoal_of_expandedColorDirHamiltonian
    (hHam : ExpandedColorDirColorHamiltonianGoal) :
    PrimitiveActivePrefixLiftAssemblyGoal :=
  primitiveActivePrefixLiftAssemblyGoal_of_projectedLift
    (primitiveActivePrefixProjectedLiftAssemblyGoal_of_expandedColorDirHamiltonian
      hHam)

def HasFeasiblePrimitiveResidues {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (hT : 2 ≤ T) (Cyl : Cylinder b m T packets) : Prop :=
  ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
    ActiveHall.FeasibleWithResidues Cyl.incidence R ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩))

/--
Primitive residue package after nonnegative count-matrix realization, but before
the Hall/slack cut estimate needed for `FeasibleWithResidues`.
-/
def HasPrimitiveResidueCountMatrix {b m T : Nat} [NeZero m]
    {packets : List (List Nat)}
    (hT : 2 ≤ T) (Cyl : Cylinder b m T packets) : Prop :=
  ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
    (∃ M : ActiveHall.CountMatrix Cyl.incidence, M.HasResidues R) ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩))

theorem activeSymboling_of_feasible_and_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (Cyl : Cylinder b m T packets)
    (R : ActiveHall.ResidueSpec m T (Fin (b + T)))
    (hFeasible : ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    ∃ A : ActiveSymboling Cyl, IsActiveSymboling A := by
  rcases
    ActiveHall.symbolingWithResidues_of_feasible_and_realization
      hHall hFeasible with
    ⟨Φ, hΦ⟩
  exact ⟨{ R := R, Φ := Φ }, ⟨hΦ⟩⟩

theorem primitiveActiveSymboling_of_feasible_primitiveResidue_and_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    (hT : 2 ≤ T) (Cyl : Cylinder b m T packets)
    (R : ActiveHall.ResidueSpec m T (Fin (b + T)))
    (hFeasible : ActiveHall.FeasibleWithResidues Cyl.incidence R)
    (hZero : ∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩))
    (hNumeric : ∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
      IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) :
    ∃ A : ActiveSymboling Cyl, IsPrimitiveActiveSymboling hT A := by
  rcases
    ActiveHall.symbolingWithResidues_of_feasible_and_realization
      hHall hFeasible with
    ⟨Φ, hΦ⟩
  exact ⟨{ R := R, Φ := Φ }, ⟨⟨hΦ⟩, hZero, hNumeric⟩⟩

theorem primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets} {hT : 2 ≤ T}
    (hResidues : HasFeasiblePrimitiveResidues hT Cyl) :
    ∃ A : ActiveSymboling Cyl, IsPrimitiveActiveSymboling hT A := by
  rcases hResidues with ⟨R, hFeasible, hZero, hNumeric⟩
  exact
    primitiveActiveSymboling_of_feasible_primitiveResidue_and_hallRealization
      hHall hT Cyl R hFeasible hZero hNumeric

theorem exists_universalResidueSpec_compatible_primitive_of_cylinder
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (hCyl : IsCylinder Cyl)
    (hdodd : Odd (b + T)) (hd3 : 3 ≤ b + T) (hmodd : Odd m) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  classical
  have hX :
      (Fintype.card (Shared.TorusVertex (b + 1) m) : ZMod m) = 0 := by
    rw [Shared.card_torusVertex]
    exact ActiveHall.zmod_natCast_pow_eq_zero_of_pos (Nat.succ_pos b)
  exact
    ActiveHall.exists_universalUnitResidueSpecOfTwoLe_compatible_primitive
      hT Cyl.incidence hdodd hd3 hmodd hCyl.active_degree_mod hX

theorem exists_universalResidueSpec_compatible_primitive_of_successor_cylinder
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (hCyl : IsCylinder Cyl) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  have hT2 : 2 ≤ T := by omega
  have hdodd : Odd (b + T) := by
    rw [hT]
    exact ⟨b, by omega⟩
  have hd3 : 3 ≤ b + T := by omega
  exact exists_universalResidueSpec_compatible_primitive_of_cylinder
    hT2 hCyl hdodd hd3 hmodd

theorem exists_universalResidueSpec_compatible_primitive_of_activeBlockData
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hT : 2 ≤ T) (D : ActiveBlockData Cyl) (hb : 0 < b)
    (hdodd : Odd (b + T)) (hd3 : 3 ≤ b + T) (hmodd : Odd m) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  classical
  have hX :
      (Fintype.card (Shared.TorusVertex (b + 1) m) : ZMod m) = 0 := by
    rw [Shared.card_torusVertex]
    exact ActiveHall.zmod_natCast_pow_eq_zero_of_pos (Nat.succ_pos b)
  exact
    ActiveHall.exists_universalUnitResidueSpecOfTwoLe_compatible_primitive
      hT Cyl.incidence hdodd hd3 hmodd (D.active_degree_mod hb) hX

theorem exists_universalResidueSpec_compatible_primitive_of_successor_activeBlockData
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (D : ActiveBlockData Cyl) :
    ∃ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
      R.RowCompatible Cyl.incidence ∧ R.ColCompatible Cyl.incidence ∧
      (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  have hT2 : 2 ≤ T := by omega
  have hbpos : 0 < b := by omega
  have hdodd : Odd (b + T) := by
    rw [hT]
    exact ⟨b, by omega⟩
  have hd3 : 3 ≤ b + T := by omega
  exact exists_universalResidueSpec_compatible_primitive_of_activeBlockData
    hT2 D hbpos hdodd hd3 hmodd

theorem primitiveResidueCountMatrix_of_successor_activeBlockData_largeMargin
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (D : ActiveBlockData Cyl)
    (hSlack : m ^ b > m * (b + T) * T) :
    HasPrimitiveResidueCountMatrix (by omega : 2 ≤ T) Cyl := by
  classical
  rcases
    exists_universalResidueSpec_compatible_primitive_of_successor_activeBlockData
      hb5 hT hmodd D with
    ⟨R, hRow, hCol, hZero, hNumeric⟩
  have hLarge :
      ∀ c : Fin (b + T),
        m * Fintype.card (Fin (b + T)) * T <
          (Cyl.incidence).colorDegree c := by
    intro c
    have hScale : m * Fintype.card (Fin (b + T)) * T < m ^ b := by
      simpa [Fintype.card_fin] using hSlack
    exact hScale.trans_le (D.active_degree_lower_bound c)
  rcases
    ActiveHall.CountMatrix.exists_with_residues_of_largeMargin
      Cyl.incidence (by omega : 0 < T) hLarge R hRow hCol with
    ⟨M, hM⟩
  exact ⟨R, ⟨M, hM⟩, hZero, hNumeric⟩

theorem feasiblePrimitiveResidues_of_successor_cylinder_feasible_compatible
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (hCyl : IsCylinder Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    HasFeasiblePrimitiveResidues (by omega : 2 ≤ T) Cyl := by
  rcases
    exists_universalResidueSpec_compatible_primitive_of_successor_cylinder
      hb5 hT hmodd hCyl with
    ⟨R, hRow, hCol, hZero, hNumeric⟩
  exact ⟨R, hFeasible R hRow hCol hZero hNumeric, hZero, hNumeric⟩

theorem feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (D : ActiveBlockData Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    HasFeasiblePrimitiveResidues (by omega : 2 ≤ T) Cyl := by
  rcases
    exists_universalResidueSpec_compatible_primitive_of_successor_activeBlockData
      hb5 hT hmodd D with
    ⟨R, hRow, hCol, hZero, hNumeric⟩
  exact ⟨R, hFeasible R hRow hCol hZero hNumeric, hZero, hNumeric⟩

theorem primitiveActiveSymboling_of_successor_cylinder_feasible_compatible
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (hCyl : IsCylinder Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    ∃ A : ActiveSymboling Cyl,
      IsPrimitiveActiveSymboling (by omega : 2 ≤ T) A := by
  exact
    primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall
      (feasiblePrimitiveResidues_of_successor_cylinder_feasible_compatible
        hb5 hT hmodd hCyl hFeasible)

theorem primitiveActiveSymboling_of_successor_activeBlockData_feasible_compatible
    (hHall : ActiveHall.HallRealizationGoal.{0, 0})
    {b m T : Nat} [NeZero m] {packets : List (List Nat)}
    {Cyl : Cylinder b m T packets}
    (hb5 : 5 ≤ b) (hT : T = b + 1) (hmodd : Odd m)
    (D : ActiveBlockData Cyl)
    (hFeasible :
      ∀ R : ActiveHall.ResidueSpec m T (Fin (b + T)),
        R.RowCompatible Cyl.incidence →
        R.ColCompatible Cyl.incidence →
        (∀ c : Fin (b + T), IsUnit (R.target c ⟨0, by omega⟩)) →
        (∀ c : Fin (b + T), ∀ σ : Fin T, 2 ≤ σ.val →
          IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) →
        ActiveHall.FeasibleWithResidues Cyl.incidence R) :
    ∃ A : ActiveSymboling Cyl,
      IsPrimitiveActiveSymboling (by omega : 2 ≤ T) A := by
  exact
    primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
      hHall
      (feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
        hb5 hT hmodd D hFeasible)

lemma list_sum_ge_mul_of_forall_ge {k : Nat} :
    ∀ {xs : List Nat}, (∀ x, x ∈ xs → k ≤ x) → k * xs.length ≤ xs.sum
  | [], _h => by simp
  | x :: xs, h => by
      have hx : k ≤ x := h x (by simp)
      have hxs : ∀ y, y ∈ xs → k ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      have ih := list_sum_ge_mul_of_forall_ge (k := k) hxs
      simp at ih ⊢
      nlinarith

lemma list_all_eq_of_sum_eq_mul {k : Nat} :
    ∀ {xs : List Nat},
      (∀ x, x ∈ xs → k ≤ x) → xs.sum = k * xs.length →
      ∀ x, x ∈ xs → x = k
  | [], _hge, _hsum, _x, hx => by simp at hx
  | x :: xs, hge, hsum, y, hy => by
      have hxge : k ≤ x := hge x (by simp)
      have hxsge : ∀ z, z ∈ xs → k ≤ z := by
        intro z hz
        exact hge z (by simp [hz])
      have htail_ge := list_sum_ge_mul_of_forall_ge (k := k) hxsge
      have hxle : x ≤ k := by
        simp at hsum
        simp at htail_ge
        nlinarith
      have hx : x = k := by omega
      have htail_sum : xs.sum = k * xs.length := by
        simp [hx] at hsum
        nlinarith
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact list_all_eq_of_sum_eq_mul (k := k) hxsge htail_sum y hy

lemma list_entries_two_or_three_of_sum_eq_two_len_add_one :
    ∀ {xs : List Nat},
      (∀ x, x ∈ xs → 2 ≤ x) → xs.sum = 2 * xs.length + 1 →
      ∀ x, x ∈ xs → x = 2 ∨ x = 3
  | [], _hge, _hsum, _x, hx => by simp at hx
  | x :: xs, hge, hsum, y, hy => by
      have hxge : 2 ≤ x := hge x (by simp)
      have hxsge : ∀ z, z ∈ xs → 2 ≤ z := by
        intro z hz
        exact hge z (by simp [hz])
      have htail_ge := list_sum_ge_mul_of_forall_ge (k := 2) hxsge
      have hxle : x ≤ 3 := by
        simp at hsum
        simp at htail_ge
        nlinarith
      have hx23 : x = 2 ∨ x = 3 := by omega
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx23
      · rcases hx23 with hx | hx
        · have htail_sum : xs.sum = 2 * xs.length + 1 := by
            simp [hx] at hsum
            nlinarith
          exact list_entries_two_or_three_of_sum_eq_two_len_add_one
            hxsge htail_sum y hy
        · have htail_sum : xs.sum = 2 * xs.length := by
            simp [hx] at hsum
            nlinarith
          left
          exact list_all_eq_of_sum_eq_mul (k := 2) hxsge htail_sum y hy

lemma list_filter_eq_three_length_eq_one_of_sum_eq_two_len_add_one :
    ∀ {xs : List Nat},
      (∀ x, x ∈ xs → 2 ≤ x) → xs.sum = 2 * xs.length + 1 →
      (xs.filter (fun x => x = 3)).length = 1
  | [], _hge, hsum => by simp at hsum
  | x :: xs, hge, hsum => by
      have hxge : 2 ≤ x := hge x (by simp)
      have hxsge : ∀ z, z ∈ xs → 2 ≤ z := by
        intro z hz
        exact hge z (by simp [hz])
      have htail_ge := list_sum_ge_mul_of_forall_ge (k := 2) hxsge
      have hxle : x ≤ 3 := by
        simp at hsum
        simp at htail_ge
        nlinarith
      have hx23 : x = 2 ∨ x = 3 := by omega
      rcases hx23 with hx | hx
      · have htail_sum : xs.sum = 2 * xs.length + 1 := by
          simp [hx] at hsum
          nlinarith
        have ih :=
          list_filter_eq_three_length_eq_one_of_sum_eq_two_len_add_one
            hxsge htail_sum
        simp [hx, ih]
      · have htail_sum : xs.sum = 2 * xs.length := by
          simp [hx] at hsum
          nlinarith
        have htail_all_two :
            ∀ y, y ∈ xs → y = 2 :=
          list_all_eq_of_sum_eq_mul (k := 2) hxsge htail_sum
        have hfilter_empty : xs.filter (fun y => y = 3) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro y hy
          rw [List.mem_filter] at hy
          have hy2 := htail_all_two y hy.1
          have hy3 : y = 3 := of_decide_eq_true hy.2
          omega
        simp [hx, hfilter_empty]

lemma packet_length_ge_two
    {m : Nat} (hm3 : 3 ≤ m) {packet : List Nat}
    (hsum : packet.sum = m)
    (hunit : ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) :
    2 ≤ packet.length := by
  cases packet with
  | nil =>
      simp at hsum
      omega
  | cons a tail =>
      cases tail with
      | nil =>
          have ha := hunit a (by simp)
          simp at hsum
          omega
      | cons _b _rest =>
          simp

lemma packet_proper_prefix_sum_coprime_of_length_two_or_three
    {m : Nat} {packet : List Nat}
    (hsum : packet.sum = m)
    (hunit : ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m)
    (hlen : packet.length = 2 ∨ packet.length = 3)
    {q : Nat} (hqpos : 0 < q) (hqproper : q < packet.length) :
    Nat.Coprime (packet.take q).sum m := by
  cases packet with
  | nil =>
      simp at hlen
  | cons a tail =>
      cases tail with
      | nil =>
          simp at hlen
      | cons b tail2 =>
          cases tail2 with
          | nil =>
              have hq : q = 1 := by
                simp at hqproper
                omega
              subst q
              have ha := hunit a (by simp)
              simpa using ha.2.2
          | cons c tail3 =>
              cases tail3 with
              | nil =>
                  have hq : q = 1 ∨ q = 2 := by
                    simp at hqproper
                    omega
                  rcases hq with rfl | rfl
                  · have ha := hunit a (by simp)
                    simpa using ha.2.2
                  · have hc := hunit c (by simp)
                    have hsumabc : a + b + c = m := by
                      simpa [Nat.add_assoc] using hsum
                    have hc_le : c ≤ m := by omega
                    have hab_eq : a + b = m - c := by omega
                    rw [show (List.take 2 [a, b, c]).sum = a + b by simp]
                    rw [hab_eq]
                    exact (Nat.coprime_self_sub_left hc_le).2 hc.2.2
              | cons _d _rest =>
                  simp at hlen

lemma packet_proper_prefix_sum_range_of_length_two_or_three
    {m : Nat} {packet : List Nat}
    (hsum : packet.sum = m)
    (hunit : ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m)
    (hlen : packet.length = 2 ∨ packet.length = 3)
    {q : Nat} (hqpos : 0 < q) (hqproper : q < packet.length) :
    0 < (packet.take q).sum ∧ (packet.take q).sum < m := by
  cases packet with
  | nil =>
      simp at hlen
  | cons a tail =>
      cases tail with
      | nil =>
          simp at hlen
      | cons b tail2 =>
          cases tail2 with
          | nil =>
              have hq : q = 1 := by
                simp at hqproper
                omega
              subst q
              have ha := hunit a (by simp)
              simpa using And.intro ha.1 ha.2.1
          | cons c tail3 =>
              cases tail3 with
              | nil =>
                  have hq : q = 1 ∨ q = 2 := by
                    simp at hqproper
                    omega
                  rcases hq with rfl | rfl
                  · have ha := hunit a (by simp)
                    simpa using And.intro ha.1 ha.2.1
                  · have hc := hunit c (by simp)
                    have hsumabc : a + b + c = m := by
                      simpa [Nat.add_assoc] using hsum
                    rw [show (List.take 2 [a, b, c]).sum = a + b by simp]
                    omega
              | cons _d _rest =>
                  simp at hlen

def SuccessorPacketLengthTwoOrThreeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets → packet.length = 2 ∨ packet.length = 3

theorem successorPacketLengthTwoOrThreeGoal :
    SuccessorPacketLengthTwoOrThreeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  let lengths : List Nat := packets.map List.length
  have hge : ∀ x, x ∈ lengths → 2 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨packet, hp, rfl⟩
    exact packet_length_ge_two hm3 (hpacketSum packet hp) (hunit packet hp)
  have hsum : lengths.sum = 2 * lengths.length + 1 := by
    dsimp [lengths]
    rw [List.length_map, hlen, htotal, hT]
    omega
  have hlengths := list_entries_two_or_three_of_sum_eq_two_len_add_one hge hsum
  intro packet hp
  exact hlengths packet.length (List.mem_map.mpr ⟨packet, hp, rfl⟩)

def SuccessorPacketLengthThreeCountGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ((packets.map List.length).filter (fun len => len = 3)).length = 1

theorem successorPacketLengthThreeCountGoal :
    SuccessorPacketLengthThreeCountGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  let lengths : List Nat := packets.map List.length
  have hge : ∀ x, x ∈ lengths → 2 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨packet, hp, rfl⟩
    exact packet_length_ge_two hm3 (hpacketSum packet hp) (hunit packet hp)
  have hsum : lengths.sum = 2 * lengths.length + 1 := by
    dsimp [lengths]
    rw [List.length_map, hlen, htotal, hT]
    omega
  exact
    list_filter_eq_three_length_eq_one_of_sum_eq_two_len_add_one hge hsum

lemma list_map_length_filter_eq_filter_length_length
    (packets : List (List Nat)) :
    ((packets.map List.length).filter (fun len => len = 3)).length
      =
    (packets.filter (fun packet => packet.length = 3)).length := by
  induction packets with
  | nil =>
      simp
  | cons packet packets ih =>
      by_cases h : packet.length = 3 <;> simp [h, ih]

lemma exists_unique_of_filter_length_eq_one {α : Type*}
    (f : α → Bool) :
    ∀ {xs : List α}, (xs.filter f).length = 1 →
      ∃ x, x ∈ xs ∧ f x = true ∧
        ∀ y, y ∈ xs → f y = true → y = x
  | [], h => by simp at h
  | x :: xs, h => by
      cases hx : f x
      · have htail : (xs.filter f).length = 1 := by
          simpa [hx] using h
        rcases exists_unique_of_filter_length_eq_one f htail with
          ⟨z, hzmem, hzf, hzuniq⟩
        refine ⟨z, by simp [hzmem], hzf, ?_⟩
        intro y hymem hyf
        simp only [List.mem_cons] at hymem
        rcases hymem with rfl | hytail
        · simp [hx] at hyf
        · exact hzuniq y hytail hyf
      · have htail_zero : (xs.filter f).length = 0 := by
          simpa [hx] using h
        refine ⟨x, by simp, hx, ?_⟩
        intro y hymem hyf
        simp only [List.mem_cons] at hymem
        rcases hymem with rfl | hytail
        · rfl
        · have hyfilter : y ∈ xs.filter f := by
            simp [hytail, hyf]
          have hfilter_nil : xs.filter f = [] :=
            List.length_eq_zero_iff.mp htail_zero
          simp [hfilter_nil] at hyfilter

def SuccessorPacketLengthThreePacketCountGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (packets.filter (fun packet => packet.length = 3)).length = 1

theorem successorPacketLengthThreePacketCountGoal :
    SuccessorPacketLengthThreePacketCountGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hlengths :=
    successorPacketLengthThreeCountGoal
      hm3 hT hlen htotal hpacketSum hunit
  rw [← list_map_length_filter_eq_filter_length_length packets]
  exact hlengths

def SuccessorPacketExistsUniqueLengthThreeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ packet, packet ∈ packets ∧ packet.length = 3 ∧
      ∀ other, other ∈ packets → other.length = 3 → other = packet

theorem successorPacketExistsUniqueLengthThreeGoal :
    SuccessorPacketExistsUniqueLengthThreeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hcount :=
    successorPacketLengthThreePacketCountGoal
      hm3 hT hlen htotal hpacketSum hunit
  rcases exists_unique_of_filter_length_eq_one
      (fun packet : List Nat => packet.length = 3) hcount with
    ⟨packet, hmem, hlen3Bool, huniq⟩
  have hlen3 : packet.length = 3 := of_decide_eq_true hlen3Bool
  refine ⟨packet, hmem, hlen3, ?_⟩
  intro other hother hother3
  exact huniq other hother (decide_eq_true hother3)

def SuccessorPacketNonExceptionalLengthTwoGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets → packet.length ≠ 3 → packet.length = 2

theorem successorPacketNonExceptionalLengthTwoGoal :
    SuccessorPacketNonExceptionalLengthTwoGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit packet hp hne
  have h23 :=
    successorPacketLengthTwoOrThreeGoal
      hm3 hT hlen htotal hpacketSum hunit packet hp
  rcases h23 with h2 | h3
  · exact h2
  · exact False.elim (hne h3)

def SuccessorPacketExceptionalShapeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ exceptional, exceptional ∈ packets ∧ exceptional.length = 3 ∧
      ∀ packet, packet ∈ packets →
        packet = exceptional ∨ packet.length = 2

theorem successorPacketExceptionalShapeGoal :
    SuccessorPacketExceptionalShapeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketExistsUniqueLengthThreeGoal
      hm3 hT hlen htotal hpacketSum hunit with
    ⟨exceptional, hexMem, hexLen, huniq⟩
  refine ⟨exceptional, hexMem, hexLen, ?_⟩
  intro packet hp
  by_cases hlen3 : packet.length = 3
  · left
    exact huniq packet hp hlen3
  · right
    exact successorPacketNonExceptionalLengthTwoGoal
      hm3 hT hlen htotal hpacketSum hunit packet hp hlen3

def SuccessorPacketProperPrefixUnitsGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        Nat.Coprime (packet.take q).sum m

theorem successorPacketProperPrefixUnitsGoal :
    SuccessorPacketProperPrefixUnitsGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hlen23 :=
    successorPacketLengthTwoOrThreeGoal hm3 hT hlen htotal hpacketSum hunit
  intro packet hp q hqpos hqproper
  exact packet_proper_prefix_sum_coprime_of_length_two_or_three
    (hpacketSum packet hp) (hunit packet hp) (hlen23 packet hp) hqpos hqproper

def SuccessorPacketPhaseSplitGoal : Prop :=
  ∀ {N b m T : Nat} [NeZero N] [NeZero m] {packets : List (List Nat)},
    m ∣ N →
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets →
      Nonempty (PacketPhaseSplit N m packet)

theorem successorPacketPhaseSplitGoal_of_packetPhaseSplitGoal
    (hSplit : PacketPhaseSplitGoal) :
    SuccessorPacketPhaseSplitGoal := by
  intro N b m T _instN _instM packets hdiv hm3 hT hlen htotal
    hpacketSum hunit packet hp
  exact
    hSplit (N := N) (m := m) (packet := packet)
      hdiv
      (hpacketSum packet hp)
      (hunit packet hp)
      (successorPacketProperPrefixUnitsGoal
        hm3 hT hlen htotal hpacketSum hunit packet hp)

def PacketPhaseSplitLengthTwoGoal : Prop :=
  ∀ {N m : Nat} [NeZero N] [NeZero m] {packet : List Nat},
    m ∣ N →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    packet.length = 2 →
    Nonempty (PacketPhaseSplit N m packet)

def PacketPhaseSplitLengthThreeGoal : Prop :=
  ∀ {N m : Nat} [NeZero N] [NeZero m] {packet : List Nat},
    m ∣ N →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    packet.length = 3 →
    Nonempty (PacketPhaseSplit N m packet)

theorem successorPacketPhaseSplitGoal_of_lengthTwoThree
    (hTwo : PacketPhaseSplitLengthTwoGoal)
    (hThree : PacketPhaseSplitLengthThreeGoal) :
    SuccessorPacketPhaseSplitGoal := by
  intro N b m T _instN _instM packets hdiv hm3 hT hlen htotal
    hpacketSum hunit packet hp
  have hlen23 :=
    successorPacketLengthTwoOrThreeGoal hm3 hT hlen htotal hpacketSum hunit
      packet hp
  rcases hlen23 with hlen2 | hlen3
  · exact hTwo hdiv (hpacketSum packet hp) (hunit packet hp) hlen2
  · exact hThree hdiv (hpacketSum packet hp) (hunit packet hp) hlen3

def SuccessorPacketPhaseSplitPowerGoal : Prop :=
  ∀ {b m T : Nat} [NeZero m] [NeZero (m ^ b)]
    {packets : List (List Nat)},
    0 < b →
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets →
      Nonempty (PacketPhaseSplit (m ^ b) m packet)

def PacketPhaseSplitLengthTwoPowerGoal : Prop :=
  ∀ {b m : Nat} [NeZero m] [NeZero (m ^ b)] {packet : List Nat},
    0 < b →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    packet.length = 2 →
    Nonempty (PacketPhaseSplit (m ^ b) m packet)

def PacketPhaseSplitLengthThreePowerGoal : Prop :=
  ∀ {b m : Nat} [NeZero m] [NeZero (m ^ b)] {packet : List Nat},
    0 < b →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    packet.length = 3 →
    Nonempty (PacketPhaseSplit (m ^ b) m packet)

def PacketPhaseIntervalPowerConstructionGoal : Prop :=
  ∀ {b m : Nat} [NeZero m] [NeZero (m ^ b)] {packet : List Nat},
    0 < b →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    Nonempty (PacketPhaseSplit (m ^ b) m packet)

def PacketPhaseSkewSingleCycleConstructionGoal : Prop :=
  ∀ {b m : Nat} [NeZero m] [NeZero (m ^ b)] {packet : List Nat},
    0 < b →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ r : Fin packet.length,
      Shared.IsSingleCycleMap
        (packetPhaseSkewStep (N := m ^ b)
          (packetPrefixPhaseSet m packet r))

def PacketPhaseSkewPeriodReturnConstructionGoal : Prop :=
  ∀ {b m : Nat} [NeZero m] [NeZero (m ^ b)] {packet : List Nat},
    0 < b →
    packet.sum = m →
    (∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ r : Fin packet.length, ∀ x : ZMod (m ^ b),
      (packetPhaseSkewStep (N := m ^ b)
        (packetPrefixPhaseSet m packet r))^[m] (0, x) =
        (0, x + (packet.get r : ZMod (m ^ b)))

def PacketPhaseSkewHitCountConstructionGoal : Prop :=
  ∀ {b m : Nat} [NeZero m] [NeZero (m ^ b)] {packet : List Nat},
    packet.sum = m →
    ∀ r : Fin packet.length,
      Finset.sum (Finset.range m)
        (fun k =>
          if (0 : ZMod m) + (k : ZMod m) ∈
              packetPrefixPhaseSet m packet r then
            (1 : ZMod (m ^ b))
          else
            0) =
        (packet.get r : ZMod (m ^ b))

theorem zmod_range_filter_card_eq
    {m : Nat} [NeZero m] (S : Finset (ZMod m)) :
    ((Finset.range m).filter
      (fun k : Nat => (k : ZMod m) ∈ S)).card = S.card := by
  classical
  apply Finset.card_bij
    (s := (Finset.range m).filter
      (fun k : Nat => (k : ZMod m) ∈ S))
    (t := S)
    (fun k _hk => (k : ZMod m))
  · intro k hk
    exact (Finset.mem_filter.mp hk).2
  · intro a ha b hb hab
    have ha_lt : a < m := by
      simpa [Finset.mem_range] using (Finset.mem_filter.mp ha).1
    have hb_lt : b < m := by
      simpa [Finset.mem_range] using (Finset.mem_filter.mp hb).1
    exact
      Nat.ModEq.eq_of_lt_of_lt
        ((ZMod.natCast_eq_natCast_iff a b m).mp hab) ha_lt hb_lt
  · intro z hz
    refine ⟨z.val, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨by simpa [Finset.mem_range] using ZMod.val_lt z,
          by simpa [ZMod.natCast_zmod_val] using hz⟩
    · exact ZMod.natCast_zmod_val z

theorem packetPhaseSkewHitCountConstructionGoal :
    PacketPhaseSkewHitCountConstructionGoal := by
  intro b m _instM _instPow packet hsum r
  have hcard :=
    zmod_range_filter_card_eq
      (S := packetPrefixPhaseSet m packet r)
  have hcard' :
      ((Finset.range m).filter
        (fun k : Nat => (k : ZMod m) ∈
          packetPrefixPhaseSet m packet r)).card = packet.get r :=
    hcard.trans (packetPrefixPhaseSet_card hsum r)
  simpa [hcard'] using
    (Finset.sum_boole
      (fun k : Nat =>
        (0 : ZMod m) + (k : ZMod m) ∈
          packetPrefixPhaseSet m packet r)
      (Finset.range m) :
        (∑ k ∈ Finset.range m,
          (if (0 : ZMod m) + (k : ZMod m) ∈
              packetPrefixPhaseSet m packet r then
            (1 : ZMod (m ^ b))
          else
            0)) =
          (((Finset.range m).filter
            (fun k : Nat =>
              (0 : ZMod m) + (k : ZMod m) ∈
                packetPrefixPhaseSet m packet r)).card : ZMod (m ^ b)))

theorem packetPhaseSkewPeriodReturnConstructionGoal_of_hitCount
    (hHit : PacketPhaseSkewHitCountConstructionGoal) :
    PacketPhaseSkewPeriodReturnConstructionGoal := by
  intro b m _instM _instPow packet _hbpos hsum _hunit r x
  apply Prod.ext
  · rw [packetPhaseSkewStep_fst_iterate]
    simp
  · rw [packetPhaseSkewStep_snd_iterate]
    rw [hHit hsum r]

theorem packetPhaseSkewPeriodReturnConstructionGoal :
    PacketPhaseSkewPeriodReturnConstructionGoal :=
  packetPhaseSkewPeriodReturnConstructionGoal_of_hitCount
    packetPhaseSkewHitCountConstructionGoal

theorem zmodPower_add_singleCycle_of_base_coprime
    {b m a : Nat} [NeZero (m ^ b)] (ha : Nat.Coprime a m) :
    Shared.IsSingleCycleMap
      (fun x : ZMod (m ^ b) => x + (a : ZMod (m ^ b))) := by
  exact
    Shared.zmod_add_single_cycle_of_coprime
      (m := m ^ b) (a := a) (ha.pow_right b)

theorem packetPhaseSkewSingleCycleConstructionGoal_of_periodReturn
    (hReturn : PacketPhaseSkewPeriodReturnConstructionGoal) :
    PacketPhaseSkewSingleCycleConstructionGoal := by
  intro b m _instM _instPow packet hbpos hsum hunit r
  exact
    packetPhaseSkewStep_singleCycle_of_return
      (N := m ^ b)
      (packetPrefixPhaseSet m packet r)
      (fun x : ZMod (m ^ b) => x + (packet.get r : ZMod (m ^ b)))
      (by
        intro x
        exact hReturn hbpos hsum hunit r x)
      (zmodPower_add_singleCycle_of_base_coprime
        ((hunit (packet.get r) (List.get_mem packet r)).2.2))

theorem packetPhaseSkewSingleCycleConstructionGoal :
    PacketPhaseSkewSingleCycleConstructionGoal :=
  packetPhaseSkewSingleCycleConstructionGoal_of_periodReturn
    (packetPhaseSkewPeriodReturnConstructionGoal_of_hitCount
      packetPhaseSkewHitCountConstructionGoal)

theorem packetPhaseIntervalPowerConstructionGoal_of_skewSingleCycle
    (hSkew : PacketPhaseSkewSingleCycleConstructionGoal) :
    PacketPhaseIntervalPowerConstructionGoal := by
  intro b m _instM _instPow packet hbpos hsum hunit
  let hdiv : m ∣ m ^ b := dvd_pow_self m hbpos.ne'
  have hpos : ∀ a, a ∈ packet → 0 < a := by
    intro a ha
    exact (hunit a ha).1
  exact
    ⟨{
      ordinary := packetPhaseIntervalOrdinary hdiv packet
      ordinary_unique := by
        intro y
        exact packetPhaseIntervalOrdinary_existsUnique hdiv hsum hpos y
      ordinary_card := by
        intro r
        exact packetPhaseIntervalOrdinary_card hdiv hsum r
      step_singleCycle := by
        intro r
        exact
          packetPhaseIntervalStep_singleCycle_of_skew
            hdiv packet r (hSkew hbpos hsum hunit r)
    }⟩

theorem packetPhaseIntervalPowerConstructionGoal :
    PacketPhaseIntervalPowerConstructionGoal :=
  packetPhaseIntervalPowerConstructionGoal_of_skewSingleCycle
    packetPhaseSkewSingleCycleConstructionGoal

theorem packetPhaseSplitLengthTwoPowerGoal_of_intervalPower
    (hInterval : PacketPhaseIntervalPowerConstructionGoal) :
    PacketPhaseSplitLengthTwoPowerGoal := by
  intro b m _instM _instPow packet hbpos hsum hunit _hlen
  exact hInterval hbpos hsum hunit

theorem packetPhaseSplitLengthTwoPowerGoal :
    PacketPhaseSplitLengthTwoPowerGoal :=
  packetPhaseSplitLengthTwoPowerGoal_of_intervalPower
    packetPhaseIntervalPowerConstructionGoal

theorem packetPhaseSplitLengthThreePowerGoal_of_intervalPower
    (hInterval : PacketPhaseIntervalPowerConstructionGoal) :
    PacketPhaseSplitLengthThreePowerGoal := by
  intro b m _instM _instPow packet hbpos hsum hunit _hlen
  exact hInterval hbpos hsum hunit

theorem packetPhaseSplitLengthThreePowerGoal :
    PacketPhaseSplitLengthThreePowerGoal :=
  packetPhaseSplitLengthThreePowerGoal_of_intervalPower
    packetPhaseIntervalPowerConstructionGoal

theorem successorPacketPhaseSplitPowerGoal_of_lengthTwoThreePower
    (hTwo : PacketPhaseSplitLengthTwoPowerGoal)
    (hThree : PacketPhaseSplitLengthThreePowerGoal) :
    SuccessorPacketPhaseSplitPowerGoal := by
  intro b m T _instM _instPow packets hbpos hm3 hT hlen htotal
    hpacketSum hunit packet hp
  have hlen23 :=
    successorPacketLengthTwoOrThreeGoal hm3 hT hlen htotal hpacketSum hunit
      packet hp
  rcases hlen23 with hlen2 | hlen3
  · exact hTwo (b := b) (m := m)
      hbpos
      (hpacketSum packet hp) (hunit packet hp) hlen2
  · exact hThree (b := b) (m := m)
      hbpos
      (hpacketSum packet hp) (hunit packet hp) hlen3

theorem successorPacketPhaseSplitPowerGoal :
    SuccessorPacketPhaseSplitPowerGoal :=
  successorPacketPhaseSplitPowerGoal_of_lengthTwoThreePower
    packetPhaseSplitLengthTwoPowerGoal
    packetPhaseSplitLengthThreePowerGoal

def SuccessorPacketProperPrefixRangeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ packet, packet ∈ packets →
      ∀ q : Nat, 0 < q → q < packet.length →
        0 < (packet.take q).sum ∧ (packet.take q).sum < m

theorem successorPacketProperPrefixRangeGoal :
    SuccessorPacketProperPrefixRangeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  have hlen23 :=
    successorPacketLengthTwoOrThreeGoal hm3 hT hlen htotal hpacketSum hunit
  intro packet hp q hqpos hqproper
  exact packet_proper_prefix_sum_range_of_length_two_or_three
    (hpacketSum packet hp) (hunit packet hp) (hlen23 packet hp) hqpos hqproper

lemma list_sum_map_length_sub_one_add_length :
    ∀ {packets : List (List Nat)},
      (∀ packet, packet ∈ packets → 1 ≤ packet.length) →
      (packets.map (fun packet => packet.length - 1)).sum + packets.length =
        (packets.map List.length).sum
  | [], _h => by simp
  | packet :: packets, h => by
      have hp : 1 ≤ packet.length := h packet (by simp)
      have htail : ∀ p, p ∈ packets → 1 ≤ p.length := by
        intro p hpMem
        exact h p (by simp [hpMem])
      have ih := list_sum_map_length_sub_one_add_length htail
      simp at ih ⊢
      omega

lemma list_sum_map_eq_sum_get {α : Type*} (f : α → Nat) :
    ∀ (xs : List α), (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum
  | [] => by simp
  | x :: xs => by
      change (∑ i : Fin (xs.length + 1), f ((x :: xs).get i)) =
        f x + (xs.map f).sum
      rw [Fin.sum_univ_succ]
      simp

def PacketPartSlot (packets : List (List Nat)) : Type :=
  Sigma fun i : Fin packets.length => Fin (packets.get i).length

instance (packets : List (List Nat)) : Fintype (PacketPartSlot packets) := by
  unfold PacketPartSlot
  infer_instance

def packetPartSlotPacket (packets : List (List Nat))
    (slot : PacketPartSlot packets) : List Nat :=
  packets.get slot.1

def packetPartSlotValue (packets : List (List Nat))
    (slot : PacketPartSlot packets) : Nat :=
  (packets.get slot.1).get slot.2

theorem packetPartSlotValue_mem (packets : List (List Nat))
    (slot : PacketPartSlot packets) :
    packetPartSlotValue packets slot ∈ packetPartSlotPacket packets slot := by
  exact List.get_mem (packets.get slot.1) slot.2

theorem packetPartSlot_card_eq_sum (packets : List (List Nat)) :
    Fintype.card (PacketPartSlot packets) =
      (packets.map List.length).sum := by
  change
    Fintype.card
      (Sigma fun i : Fin packets.length => Fin (packets.get i).length) =
        (packets.map List.length).sum
  rw [Fintype.card_sigma]
  simpa only [Fintype.card_fin] using
    list_sum_map_eq_sum_get (fun packet : List Nat => packet.length)
      packets

theorem packetPartSlot_false_card_at_state
    {N m : Nat} [NeZero N] [NeZero m]
    (packets : List (List Nat))
    (S : ∀ i : Fin packets.length,
      PacketPhaseSplit N m (packets.get i))
    (rank : Fin packets.length → ZMod N) (a : ZMod m) :
    ((Finset.univ : Finset (PacketPartSlot packets)).filter
      (fun slot =>
        (S slot.1).ordinary slot.2 (rank slot.1, a) = false)).card =
      (packets.map (fun packet => packet.length - 1)).sum := by
  classical
  let e :
      {slot : PacketPartSlot packets //
        (S slot.1).ordinary slot.2 (rank slot.1, a) = false} ≃
        Sigma fun i : Fin packets.length =>
          {r : Fin (packets.get i).length //
            (S i).ordinary r (rank i, a) = false} :=
  {
    toFun := fun slot =>
      ⟨slot.1.1, ⟨slot.1.2, slot.2⟩⟩
    invFun := fun slot =>
      ⟨⟨slot.1, slot.2.1⟩, slot.2.2⟩
    left_inv := by
      intro slot
      rfl
    right_inv := by
      intro slot
      rfl
  }
  have hsub :
      Fintype.card
        {slot : PacketPartSlot packets //
          (S slot.1).ordinary slot.2 (rank slot.1, a) = false} =
      ((Finset.univ : Finset (PacketPartSlot packets)).filter
        (fun slot =>
          (S slot.1).ordinary slot.2 (rank slot.1, a) = false)).card := by
    exact Fintype.card_subtype _
  rw [← hsub, Fintype.card_congr e, Fintype.card_sigma]
  simpa using
    (show
      (∑ i : Fin packets.length,
        Fintype.card
          {r : Fin (packets.get i).length //
            (S i).ordinary r (rank i, a) = false}) =
        (packets.map (fun packet => packet.length - 1)).sum from by
          calc
            (∑ i : Fin packets.length,
              Fintype.card
                {r : Fin (packets.get i).length //
                  (S i).ordinary r (rank i, a) = false})
                =
              ∑ i : Fin packets.length,
                ((Finset.univ : Finset (Fin (packets.get i).length)).filter
                  (fun r => (S i).ordinary r (rank i, a) = false)).card := by
                apply Finset.sum_congr rfl
                intro i _hi
                exact Fintype.card_subtype _
            _ =
              ∑ i : Fin packets.length,
                ((packets.get i).length - 1) := by
                apply Finset.sum_congr rfl
                intro i _hi
                exact (S i).ordinary_false_card_at_state (rank i, a)
            _ =
              (packets.map (fun packet => packet.length - 1)).sum := by
                exact list_sum_map_eq_sum_get
                  (fun packet : List Nat => packet.length - 1) packets)

theorem packetPartSlot_false_card_at_state_successor
    {b T N m : Nat} [NeZero N] [NeZero m]
    (packets : List (List Nat))
    (hm3 : 3 ≤ m)
    (hlen : packets.length = b)
    (htotal : (packets.map List.length).sum = b + T)
    (hpacketSum : ∀ packet, packet ∈ packets → packet.sum = m)
    (hunit :
      ∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m)
    (S : ∀ i : Fin packets.length,
      PacketPhaseSplit N m (packets.get i))
    (rank : Fin packets.length → ZMod N) (a : ZMod m) :
    ((Finset.univ : Finset (PacketPartSlot packets)).filter
      (fun slot =>
        (S slot.1).ordinary slot.2 (rank slot.1, a) = false)).card = T := by
  rw [packetPartSlot_false_card_at_state packets S rank a]
  have hge : ∀ packet, packet ∈ packets → 1 ≤ packet.length := by
    intro packet hp
    have htwo : 2 ≤ packet.length :=
      packet_length_ge_two hm3 (hpacketSum packet hp) (hunit packet hp)
    omega
  have hsum :=
    list_sum_map_length_sub_one_add_length (packets := packets) hge
  rw [hlen, htotal] at hsum
  omega

theorem packetPartColor_false_card_at_state_successor
    {b T N m : Nat} [NeZero N] [NeZero m]
    (packets : List (List Nat))
    (e : PacketPartSlot packets ≃ Fin (b + T))
    (hm3 : 3 ≤ m)
    (hlen : packets.length = b)
    (htotal : (packets.map List.length).sum = b + T)
    (hpacketSum : ∀ packet, packet ∈ packets → packet.sum = m)
    (hunit :
      ∀ packet, packet ∈ packets →
        ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m)
    (S : ∀ i : Fin packets.length,
      PacketPhaseSplit N m (packets.get i))
    (rank : Fin packets.length → ZMod N) (a : ZMod m) :
    ((Finset.univ : Finset (Fin (b + T))).filter
      (fun c =>
        (S (e.symm c).1).ordinary (e.symm c).2
          (rank (e.symm c).1, a) = false)).card = T := by
  classical
  let P : PacketPartSlot packets → Prop := fun slot =>
    (S slot.1).ordinary slot.2 (rank slot.1, a) = false
  let eSub :
      {c : Fin (b + T) // P (e.symm c)} ≃
        {slot : PacketPartSlot packets // P slot} :=
  {
    toFun := fun c => ⟨e.symm c.1, c.2⟩
    invFun := fun slot => ⟨e slot.1, by simpa [P] using slot.2⟩
    left_inv := by
      intro c
      apply Subtype.ext
      simp
    right_inv := by
      intro slot
      apply Subtype.ext
      simp
  }
  have hcolor :
      Fintype.card {c : Fin (b + T) // P (e.symm c)} =
      ((Finset.univ : Finset (Fin (b + T))).filter
        (fun c => P (e.symm c))).card := by
    exact Fintype.card_subtype _
  have hslot :
      Fintype.card {slot : PacketPartSlot packets // P slot} =
      ((Finset.univ : Finset (PacketPartSlot packets)).filter
        (fun slot => P slot)).card := by
    exact Fintype.card_subtype _
  rw [← hcolor, Fintype.card_congr eSub, hslot]
  exact packetPartSlot_false_card_at_state_successor
    packets hm3 hlen htotal hpacketSum hunit S rank a

def SuccessorPacketPartSlotCardGoal : Prop :=
  ∀ {b T : Nat} {packets : List (List Nat)},
    packets.length = b →
    (packets.map List.length).sum = b + T →
    Fintype.card (PacketPartSlot packets) = b + T

theorem successorPacketPartSlotCardGoal :
    SuccessorPacketPartSlotCardGoal := by
  intro b T packets _hlen htotal
  rw [packetPartSlot_card_eq_sum, htotal]

def SuccessorPacketPartSlotEquivGoal : Prop :=
  ∀ {b T : Nat} {packets : List (List Nat)},
    packets.length = b →
    (packets.map List.length).sum = b + T →
    Nonempty (PacketPartSlot packets ≃ Fin (b + T))

theorem successorPacketPartSlotEquivGoal :
    SuccessorPacketPartSlotEquivGoal := by
  intro b T packets hlen htotal
  have hcard :
      Fintype.card (PacketPartSlot packets) =
        Fintype.card (Fin (b + T)) := by
    rw [successorPacketPartSlotCardGoal hlen htotal]
    simp
  exact ⟨Fintype.equivOfCardEq hcard⟩

def SuccessorPacketPartSlotUnitsGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ slot : PacketPartSlot packets,
      0 < packetPartSlotValue packets slot ∧
        packetPartSlotValue packets slot < m ∧
        Nat.Coprime (packetPartSlotValue packets slot) m

theorem successorPacketPartSlotUnitsGoal :
    SuccessorPacketPartSlotUnitsGoal := by
  intro _b _m _T packets _hlen _htotal hunit slot
  exact hunit
    (packetPartSlotPacket packets slot)
    (List.get_mem packets slot.1)
    (packetPartSlotValue packets slot)
    (packetPartSlotValue_mem packets slot)

def PacketPrefixSlot (packets : List (List Nat)) : Type :=
  Sigma fun i : Fin packets.length => Fin ((packets.get i).length - 1)

instance (packets : List (List Nat)) : Fintype (PacketPrefixSlot packets) := by
  unfold PacketPrefixSlot
  infer_instance

def packetPrefixSlotPacket (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) : List Nat :=
  packets.get slot.1

def packetPrefixSlotPrefixLength (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) : Nat :=
  slot.2.val + 1

theorem packetPrefixSlotPrefixLength_pos (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) :
    0 < packetPrefixSlotPrefixLength packets slot := by
  simp [packetPrefixSlotPrefixLength]

theorem packetPrefixSlotPrefixLength_lt (packets : List (List Nat))
    (slot : PacketPrefixSlot packets) :
    packetPrefixSlotPrefixLength packets slot <
      (packetPrefixSlotPacket packets slot).length := by
  dsimp [packetPrefixSlotPrefixLength, packetPrefixSlotPacket,
    PacketPrefixSlot] at *
  exact Nat.add_lt_of_lt_sub slot.2.isLt

theorem packetPrefixSlot_card_eq_sum (packets : List (List Nat)) :
    Fintype.card (PacketPrefixSlot packets) =
      (packets.map (fun packet => packet.length - 1)).sum := by
  change
    Fintype.card
      (Sigma fun i : Fin packets.length => Fin ((packets.get i).length - 1)) =
        (packets.map (fun packet => packet.length - 1)).sum
  rw [Fintype.card_sigma]
  simpa using
    list_sum_map_eq_sum_get (fun packet : List Nat => packet.length - 1)
      packets

def SuccessorPacketProperPrefixSlotCountGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    (packets.map (fun packet => packet.length - 1)).sum = T

theorem successorPacketProperPrefixSlotCountGoal :
    SuccessorPacketProperPrefixSlotCountGoal := by
  intro b m T packets hm3 hlen htotal hpacketSum hunit
  have hge : ∀ packet, packet ∈ packets → 1 ≤ packet.length := by
    intro packet hp
    have htwo : 2 ≤ packet.length :=
      packet_length_ge_two hm3 (hpacketSum packet hp) (hunit packet hp)
    omega
  have hsum :=
    list_sum_map_length_sub_one_add_length (packets := packets) hge
  rw [hlen, htotal] at hsum
  omega

def SuccessorPacketPrefixSlotCardGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    Fintype.card (PacketPrefixSlot packets) = T

theorem successorPacketPrefixSlotCardGoal :
    SuccessorPacketPrefixSlotCardGoal := by
  intro b m T packets hm3 hlen htotal hpacketSum hunit
  rw [packetPrefixSlot_card_eq_sum]
  exact successorPacketProperPrefixSlotCountGoal
    hm3 hlen htotal hpacketSum hunit

def SuccessorPacketPrefixSlotEquivGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    Nonempty (PacketPrefixSlot packets ≃ Fin T)

theorem successorPacketPrefixSlotEquivGoal :
    SuccessorPacketPrefixSlotEquivGoal := by
  intro b m T packets hm3 hlen htotal hpacketSum hunit
  have hcard : Fintype.card (PacketPrefixSlot packets) = Fintype.card (Fin T) := by
    rw [successorPacketPrefixSlotCardGoal hm3 hlen htotal hpacketSum hunit]
    simp
  exact ⟨Fintype.equivOfCardEq hcard⟩

def SuccessorPacketPrefixSlotUnitsGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ slot : PacketPrefixSlot packets,
      Nat.Coprime
        ((packetPrefixSlotPacket packets slot).take
          (packetPrefixSlotPrefixLength packets slot)).sum m

theorem successorPacketPrefixSlotUnitsGoal :
    SuccessorPacketPrefixSlotUnitsGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit slot
  exact successorPacketProperPrefixUnitsGoal
    hm3 hT hlen htotal hpacketSum hunit
    (packetPrefixSlotPacket packets slot)
    (List.get_mem packets slot.1)
    (packetPrefixSlotPrefixLength packets slot)
    (packetPrefixSlotPrefixLength_pos packets slot)
    (packetPrefixSlotPrefixLength_lt packets slot)

def SuccessorPacketPrefixSlotRangeGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∀ slot : PacketPrefixSlot packets,
      0 <
          ((packetPrefixSlotPacket packets slot).take
            (packetPrefixSlotPrefixLength packets slot)).sum ∧
        ((packetPrefixSlotPacket packets slot).take
            (packetPrefixSlotPrefixLength packets slot)).sum < m

theorem successorPacketPrefixSlotRangeGoal :
    SuccessorPacketPrefixSlotRangeGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit slot
  exact successorPacketProperPrefixRangeGoal
    hm3 hT hlen htotal hpacketSum hunit
    (packetPrefixSlotPacket packets slot)
    (List.get_mem packets slot.1)
    (packetPrefixSlotPrefixLength packets slot)
    (packetPrefixSlotPrefixLength_pos packets slot)
    (packetPrefixSlotPrefixLength_lt packets slot)

def SuccessorPacketTailCarryDataGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ carry : Fin T → Nat,
      ∀ σ : Fin T, 0 < carry σ ∧ carry σ < m ∧ Nat.Coprime (carry σ) m

theorem successorPacketTailCarryDataGoal :
    SuccessorPacketTailCarryDataGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketPrefixSlotEquivGoal
      hm3 hlen htotal hpacketSum hunit with ⟨e⟩
  let carry : Fin T → Nat := fun σ =>
    ((packetPrefixSlotPacket packets (e.symm σ)).take
      (packetPrefixSlotPrefixLength packets (e.symm σ))).sum
  refine ⟨carry, ?_⟩
  intro σ
  have hrange :=
    successorPacketPrefixSlotRangeGoal
      hm3 hT hlen htotal hpacketSum hunit (e.symm σ)
  have hunitCarry :=
    successorPacketPrefixSlotUnitsGoal
      hm3 hT hlen htotal hpacketSum hunit (e.symm σ)
  exact ⟨hrange.1, hrange.2, hunitCarry⟩

structure PacketTailCarryData (m T : Nat) (packets : List (List Nat)) where
  slotOf : Fin T ≃ PacketPrefixSlot packets
  carry : Fin T → Nat
  carry_eq :
    ∀ σ : Fin T,
      carry σ =
        ((packetPrefixSlotPacket packets (slotOf σ)).take
          (packetPrefixSlotPrefixLength packets (slotOf σ))).sum
  carry_pos : ∀ σ : Fin T, 0 < carry σ
  carry_lt : ∀ σ : Fin T, carry σ < m
  carry_coprime : ∀ σ : Fin T, Nat.Coprime (carry σ) m

namespace PacketTailCarryData

def residue {m T : Nat} {packets : List (List Nat)}
    (D : PacketTailCarryData m T packets) : Fin T → ZMod m :=
  fun σ => (D.carry σ : ZMod m)

theorem residue_isUnit {m T : Nat} {packets : List (List Nat)}
    (D : PacketTailCarryData m T packets) (σ : Fin T) :
    IsUnit (D.residue σ) := by
  exact (ZMod.isUnit_iff_coprime (D.carry σ) m).2 (D.carry_coprime σ)

end PacketTailCarryData

def SuccessorPacketTailCarryStructureGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    Nonempty (PacketTailCarryData m T packets)

theorem successorPacketTailCarryStructureGoal :
    SuccessorPacketTailCarryStructureGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketPrefixSlotEquivGoal
      hm3 hlen htotal hpacketSum hunit with ⟨e⟩
  let slotOf : Fin T ≃ PacketPrefixSlot packets := e.symm
  let carry : Fin T → Nat := fun σ =>
    ((packetPrefixSlotPacket packets (slotOf σ)).take
      (packetPrefixSlotPrefixLength packets (slotOf σ))).sum
  have hRange :
      ∀ σ : Fin T, 0 < carry σ ∧ carry σ < m := by
    intro σ
    exact successorPacketPrefixSlotRangeGoal
      hm3 hT hlen htotal hpacketSum hunit (slotOf σ)
  have hCoprime :
      ∀ σ : Fin T, Nat.Coprime (carry σ) m := by
    intro σ
    exact successorPacketPrefixSlotUnitsGoal
      hm3 hT hlen htotal hpacketSum hunit (slotOf σ)
  refine ⟨{
    slotOf := slotOf
    carry := carry
    carry_eq := ?_
    carry_pos := ?_
    carry_lt := ?_
    carry_coprime := hCoprime
  }⟩
  · intro σ
    rfl
  · intro σ
    exact (hRange σ).1
  · intro σ
    exact (hRange σ).2

def SuccessorPacketTailCarryResidueUnitsGoal : Prop :=
  ∀ {b m T : Nat} {packets : List (List Nat)},
    3 ≤ m →
    T = b + 1 →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    ∃ carry : Fin T → ZMod m,
      ∀ σ : Fin T, IsUnit (carry σ)

theorem successorPacketTailCarryResidueUnitsGoal :
    SuccessorPacketTailCarryResidueUnitsGoal := by
  intro b m T packets hm3 hT hlen htotal hpacketSum hunit
  rcases successorPacketTailCarryDataGoal
      hm3 hT hlen htotal hpacketSum hunit with ⟨carryNat, hcarry⟩
  refine ⟨fun σ => (carryNat σ : ZMod m), ?_⟩
  intro σ
  exact (ZMod.isUnit_iff_coprime (carryNat σ) m).2 (hcarry σ).2.2

end BaseTail
end Concrete
end RoundComposite
