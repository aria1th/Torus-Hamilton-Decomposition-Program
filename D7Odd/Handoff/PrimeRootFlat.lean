import D7Odd.Handoff.PrimeRoot

namespace D7Odd
namespace Handoff
namespace PrimeRoot
namespace PrimeDimension

def addQ (D : PrimeDimension) (m : Nat) (i : D.Direction)
    (w : D.Vec m) : D.Vec m :=
  w + D.q m i

def subQ (D : PrimeDimension) (m : Nat) (i : D.Direction)
    (w : D.Vec m) : D.Vec m :=
  w - D.q m i

theorem sum_add (D : PrimeDimension) (m : Nat)
    (x y : D.Vec m) :
    D.sum m (x + y) = D.sum m x + D.sum m y := by
  simp [sum, Finset.sum_add_distrib]

theorem sum_sub (D : PrimeDimension) (m : Nat)
    (x y : D.Vec m) :
    D.sum m (x - y) = D.sum m x - D.sum m y := by
  simp [sum, Finset.sum_sub_distrib]

theorem sum_e (D : PrimeDimension) (m : Nat) (i : D.Direction) :
    D.sum m (D.e m i) = 1 := by
  simp [sum, e]

theorem sum_q_zero (D : PrimeDimension) (m : Nat) (i : D.Direction) :
    D.sum m (D.q m i) = 0 := by
  calc
    D.sum m (D.q m i) =
        D.sum m (D.e m i) - D.sum m (D.e m D.sink) := by
      simp [q, sum, Finset.sum_sub_distrib]
    _ = 0 := by
      rw [sum_e, sum_e]
      simp

def addQRoot (D : PrimeDimension) (m : Nat)
    (i : D.Direction) (w : D.RootState m) : D.RootState m :=
  ⟨D.addQ m i w.1, by
    unfold Root addQ
    rw [D.sum_add, w.2, D.sum_q_zero]
    simp⟩

def subQRoot (D : PrimeDimension) (m : Nat)
    (i : D.Direction) (w : D.RootState m) : D.RootState m :=
  ⟨D.subQ m i w.1, by
    unfold Root subQ
    rw [D.sum_sub, w.2, D.sum_q_zero]
    simp⟩

theorem subQRoot_addQRoot (D : PrimeDimension) {m : Nat}
    (i : D.Direction) (w : D.RootState m) :
    D.subQRoot m i (D.addQRoot m i w) = w := by
  apply Subtype.ext
  ext j
  simp [subQRoot, addQRoot, subQ, addQ]

theorem addQRoot_subQRoot (D : PrimeDimension) {m : Nat}
    (i : D.Direction) (w : D.RootState m) :
    D.addQRoot m i (D.subQRoot m i w) = w := by
  apply Subtype.ext
  ext j
  simp [subQRoot, addQRoot, subQ, addQ]

theorem addQRoot_bijective (D : PrimeDimension) {m : Nat}
    (i : D.Direction) :
    Function.Bijective (D.addQRoot m i) :=
  Handoff.bijective_of_inverse (D.addQRoot m i) (D.subQRoot m i)
    (D.subQRoot_addQRoot i) (D.addQRoot_subQRoot i)

structure RootFlatSchedule (D : PrimeDimension) (m : Nat) where
  dir : ZMod m → D.RootState m → D.Color → D.Direction

namespace RootFlatSchedule

def rowLatin {D : PrimeDimension} {m : Nat}
    (S : D.RootFlatSchedule m) : Prop :=
  ∀ t w, Function.Bijective fun c : D.Color => S.dir t w c

def layerMap {D : PrimeDimension} {m : Nat}
    (S : D.RootFlatSchedule m) (t : ZMod m) (c : D.Color) :
    D.RootState m → D.RootState m :=
  fun w => D.addQRoot m (S.dir t w c) w

def layerBijective {D : PrimeDimension} {m : Nat}
    (S : D.RootFlatSchedule m) : Prop :=
  ∀ t c, Function.Bijective (S.layerMap t c)

def returnMap {D : PrimeDimension} {m : Nat} [NeZero m]
    (S : D.RootFlatSchedule m) (c : D.Color) :
    D.RootState m → D.RootState m :=
  fun w => ((List.range m).foldl
    (fun x (t : Nat) => S.layerMap (t : ZMod m) c x) w)

def returnsSingleCycle {D : PrimeDimension} {m : Nat} [NeZero m]
    (S : D.RootFlatSchedule m) : Prop :=
  ∀ c : D.Color, Handoff.IsSingleCycleMap (S.returnMap c)

end RootFlatSchedule

structure RootFlatCertificate (D : PrimeDimension) (m : Nat) [NeZero m] where
  schedule : D.RootFlatSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle

def HamiltonDecomposition (D : PrimeDimension) (m : Nat) [NeZero m] : Prop :=
  Nonempty (D.RootFlatCertificate m)

theorem certificate_implies_hamilton (D : PrimeDimension)
    {m : Nat} [NeZero m] (cert : D.RootFlatCertificate m) :
    D.HamiltonDecomposition m := by
  exact ⟨cert⟩

end PrimeDimension
end PrimeRoot
end Handoff
end D7Odd
