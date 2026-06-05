import EvenV11.WordSkew

namespace EvenV11
namespace FiniteCertificate

structure RankCycleCertificate (α : Type*) (N : Nat) [NeZero N] where
  step : α → α
  rank : α → ZMod N
  rankBijective : Function.Bijective rank
  rankStep : ∀ x : α, rank (step x) = rank x + 1

theorem rankCycleCertificate_singleCycle
    {α : Type*} {N : Nat} [NeZero N]
    (C : RankCycleCertificate α N) :
    Shared.IsSingleCycleMap C.step :=
  Shared.single_cycle_of_zmod_rank
    C.step C.rank C.rankBijective C.rankStep

theorem rankCycleCertificate_iterate_rank
    {α : Type*} {N : Nat} [NeZero N]
    (C : RankCycleCertificate α N) :
    ∀ n : Nat, ∀ x : α, C.rank (C.step^[n] x) = C.rank x + (n : ZMod N) :=
  Shared.iterate_rank_add_one C.step C.rank C.rankStep

structure IndexedOrbitCertificate (α : Type*) (N : Nat) [NeZero N] where
  step : α → α
  orbit : Fin N ≃ α
  stepOrbit : ∀ i : Fin N, orbit (i + 1) = step (orbit i)

noncomputable def IndexedOrbitCertificate.toCycleCoordinate
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) :
    Shared.CycleCoordinate N C.step :=
  Shared.CycleCoordinate.ofFinEquiv C.orbit C.stepOrbit

theorem indexedOrbitCertificate_singleCycle
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) :
    Shared.IsSingleCycleMap C.step :=
  Shared.CycleCoordinate.singleCycle C.toCycleCoordinate

theorem indexedOrbitCertificate_rankStep
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (x : α) :
    C.toCycleCoordinate.equiv.symm (C.step x) =
      C.toCycleCoordinate.equiv.symm x + 1 :=
  Shared.CycleCoordinate.rank_step C.toCycleCoordinate x

theorem indexedOrbitCertificate_iterate_rank
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (n : Nat) (x : α) :
    C.toCycleCoordinate.equiv.symm ((C.step^[n]) x) =
      C.toCycleCoordinate.equiv.symm x + (n : ZMod N) :=
  Shared.iterate_rank_add_one C.step C.toCycleCoordinate.equiv.symm
    (indexedOrbitCertificate_rankStep C) n x

theorem indexedOrbitCertificate_iterate_orbit
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (i : Fin N) :
    ∀ n : Nat, (C.step^[n]) (C.orbit i) =
      C.orbit (i + Fin.ofNat N n) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [← C.stepOrbit]
      congr 1
      ext
      simp [Fin.val_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem indexedOrbitCertificate_coordinate_orbit
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (i : Fin N) :
    C.orbit.symm (C.orbit i) = i := by
  simp

theorem indexedOrbitCertificate_coordinate_iterate_orbit
    {α : Type*} {N : Nat} [NeZero N]
    (C : IndexedOrbitCertificate α N) (i : Fin N) (n : Nat) :
    C.orbit.symm ((C.step^[n]) (C.orbit i)) =
      i + Fin.ofNat N n := by
  rw [indexedOrbitCertificate_iterate_orbit]
  simp

structure WordRankCycleCertificate
    (ι α : Type*) (N : Nat) [NeZero N] where
  symbolStep : ι → α → α
  word : List ι
  rank : α → ZMod N
  rankBijective : Function.Bijective rank
  rankStep :
    ∀ x : α, rank (wordEval symbolStep word x) = rank x + 1

def WordRankCycleCertificate.toRankCycleCertificate
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : WordRankCycleCertificate ι α N) :
    RankCycleCertificate α N where
  step := wordEval C.symbolStep C.word
  rank := C.rank
  rankBijective := C.rankBijective
  rankStep := C.rankStep

theorem wordRankCycleCertificate_singleCycle
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : WordRankCycleCertificate ι α N) :
    Shared.IsSingleCycleMap (wordEval C.symbolStep C.word) :=
  rankCycleCertificate_singleCycle C.toRankCycleCertificate

theorem wordRankCycleCertificate_iterate_rank
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : WordRankCycleCertificate ι α N) :
    ∀ n : Nat, ∀ x : α,
      C.rank ((wordEval C.symbolStep C.word)^[n] x) =
        C.rank x + (n : ZMod N) :=
  rankCycleCertificate_iterate_rank C.toRankCycleCertificate

structure IndexedWordOrbitCertificate
    (ι α : Type*) (N : Nat) [NeZero N] where
  symbolStep : ι → α → α
  word : List ι
  orbit : Fin N ≃ α
  stepOrbit :
    ∀ i : Fin N, orbit (i + 1) = wordEval symbolStep word (orbit i)

def IndexedWordOrbitCertificate.toIndexedOrbitCertificate
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) :
    IndexedOrbitCertificate α N where
  step := wordEval C.symbolStep C.word
  orbit := C.orbit
  stepOrbit := C.stepOrbit

theorem indexedWordOrbitCertificate_singleCycle
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) :
    Shared.IsSingleCycleMap (wordEval C.symbolStep C.word) :=
  indexedOrbitCertificate_singleCycle C.toIndexedOrbitCertificate

theorem indexedWordOrbitCertificate_rankStep
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (x : α) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (wordEval C.symbolStep C.word x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x + 1 :=
  indexedOrbitCertificate_rankStep C.toIndexedOrbitCertificate x

theorem indexedWordOrbitCertificate_iterate_rank
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (n : Nat) (x : α) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (((wordEval C.symbolStep C.word)^[n]) x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x +
        (n : ZMod N) :=
  indexedOrbitCertificate_iterate_rank C.toIndexedOrbitCertificate n x

theorem indexedWordOrbitCertificate_iterate_orbit
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (i : Fin N) :
    ∀ n : Nat, ((wordEval C.symbolStep C.word)^[n]) (C.orbit i) =
      C.orbit (i + Fin.ofNat N n) :=
  indexedOrbitCertificate_iterate_orbit C.toIndexedOrbitCertificate i

theorem indexedWordOrbitCertificate_coordinate_orbit
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (i : Fin N) :
    C.orbit.symm (C.orbit i) = i :=
  indexedOrbitCertificate_coordinate_orbit C.toIndexedOrbitCertificate i

theorem indexedWordOrbitCertificate_coordinate_iterate_orbit
    {ι α : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordOrbitCertificate ι α N) (i : Fin N) (n : Nat) :
    C.orbit.symm (((wordEval C.symbolStep C.word)^[n]) (C.orbit i)) =
      i + Fin.ofNat N n :=
  indexedOrbitCertificate_coordinate_iterate_orbit
    C.toIndexedOrbitCertificate i n

structure WordSkewRankCycleCertificate
    (Symbol Base Fiber : Type*) (N : Nat) [NeZero N] where
  baseStep : Symbol → Base → Base
  fiberStep : Symbol → Base → Fiber → Fiber
  word : List Symbol
  rank : Base × Fiber → ZMod N
  rankBijective : Function.Bijective rank
  rankStep :
    ∀ x : Base × Fiber,
      rank (wordSkewEval baseStep fiberStep word x) = rank x + 1

def WordSkewRankCycleCertificate.toRankCycleCertificate
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : WordSkewRankCycleCertificate Symbol Base Fiber N) :
    RankCycleCertificate (Base × Fiber) N where
  step := wordSkewEval C.baseStep C.fiberStep C.word
  rank := C.rank
  rankBijective := C.rankBijective
  rankStep := C.rankStep

theorem wordSkewRankCycleCertificate_singleCycle
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : WordSkewRankCycleCertificate Symbol Base Fiber N) :
    Shared.IsSingleCycleMap (wordSkewEval C.baseStep C.fiberStep C.word) :=
  rankCycleCertificate_singleCycle C.toRankCycleCertificate

theorem wordSkewRankCycleCertificate_iterate_rank
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : WordSkewRankCycleCertificate Symbol Base Fiber N) :
    ∀ n : Nat, ∀ x : Base × Fiber,
      C.rank ((wordSkewEval C.baseStep C.fiberStep C.word)^[n] x) =
        C.rank x + (n : ZMod N) :=
  rankCycleCertificate_iterate_rank C.toRankCycleCertificate

structure IndexedWordSkewOrbitCertificate
    (Symbol Base Fiber : Type*) (N : Nat) [NeZero N] where
  baseStep : Symbol → Base → Base
  fiberStep : Symbol → Base → Fiber → Fiber
  word : List Symbol
  orbit : Fin N ≃ Base × Fiber
  stepOrbit :
    ∀ i : Fin N,
      orbit (i + 1) =
        wordSkewEval baseStep fiberStep word (orbit i)

def IndexedWordSkewOrbitCertificate.toIndexedOrbitCertificate
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N) :
    IndexedOrbitCertificate (Base × Fiber) N where
  step := wordSkewEval C.baseStep C.fiberStep C.word
  orbit := C.orbit
  stepOrbit := C.stepOrbit

theorem indexedWordSkewOrbitCertificate_singleCycle
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N) :
    Shared.IsSingleCycleMap (wordSkewEval C.baseStep C.fiberStep C.word) :=
  indexedOrbitCertificate_singleCycle C.toIndexedOrbitCertificate

theorem indexedWordSkewOrbitCertificate_rankStep
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N)
    (x : Base × Fiber) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (wordSkewEval C.baseStep C.fiberStep C.word x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x + 1 :=
  indexedOrbitCertificate_rankStep C.toIndexedOrbitCertificate x

theorem indexedWordSkewOrbitCertificate_iterate_rank
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N)
    (n : Nat) (x : Base × Fiber) :
    C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm
        (((wordSkewEval C.baseStep C.fiberStep C.word)^[n]) x) =
      C.toIndexedOrbitCertificate.toCycleCoordinate.equiv.symm x +
        (n : ZMod N) :=
  indexedOrbitCertificate_iterate_rank C.toIndexedOrbitCertificate n x

theorem indexedWordSkewOrbitCertificate_iterate_orbit
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N) (i : Fin N) :
    ∀ n : Nat,
      ((wordSkewEval C.baseStep C.fiberStep C.word)^[n])
          (C.orbit i) =
        C.orbit (i + Fin.ofNat N n) :=
  indexedOrbitCertificate_iterate_orbit C.toIndexedOrbitCertificate i

theorem indexedWordSkewOrbitCertificate_coordinate_orbit
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N) (i : Fin N) :
    C.orbit.symm (C.orbit i) = i :=
  indexedOrbitCertificate_coordinate_orbit C.toIndexedOrbitCertificate i

theorem indexedWordSkewOrbitCertificate_coordinate_iterate_orbit
    {Symbol Base Fiber : Type*} {N : Nat} [NeZero N]
    (C : IndexedWordSkewOrbitCertificate Symbol Base Fiber N)
    (i : Fin N) (n : Nat) :
    C.orbit.symm
        (((wordSkewEval C.baseStep C.fiberStep C.word)^[n])
          (C.orbit i)) =
      i + Fin.ofNat N n :=
  indexedOrbitCertificate_coordinate_iterate_orbit
    C.toIndexedOrbitCertificate i n

end FiniteCertificate

export FiniteCertificate
  (RankCycleCertificate rankCycleCertificate_singleCycle
   rankCycleCertificate_iterate_rank
   IndexedOrbitCertificate
   IndexedOrbitCertificate.toCycleCoordinate
   indexedOrbitCertificate_singleCycle
   indexedOrbitCertificate_rankStep
   indexedOrbitCertificate_iterate_rank
   indexedOrbitCertificate_iterate_orbit
   indexedOrbitCertificate_coordinate_orbit
   indexedOrbitCertificate_coordinate_iterate_orbit
   WordRankCycleCertificate
   WordRankCycleCertificate.toRankCycleCertificate
   wordRankCycleCertificate_singleCycle
   wordRankCycleCertificate_iterate_rank
   IndexedWordOrbitCertificate
   IndexedWordOrbitCertificate.toIndexedOrbitCertificate
   indexedWordOrbitCertificate_singleCycle
   indexedWordOrbitCertificate_rankStep
   indexedWordOrbitCertificate_iterate_rank
   indexedWordOrbitCertificate_iterate_orbit
   indexedWordOrbitCertificate_coordinate_orbit
   indexedWordOrbitCertificate_coordinate_iterate_orbit
   WordSkewRankCycleCertificate
   WordSkewRankCycleCertificate.toRankCycleCertificate
   wordSkewRankCycleCertificate_singleCycle
   wordSkewRankCycleCertificate_iterate_rank
   IndexedWordSkewOrbitCertificate
   IndexedWordSkewOrbitCertificate.toIndexedOrbitCertificate
   indexedWordSkewOrbitCertificate_singleCycle
   indexedWordSkewOrbitCertificate_rankStep
   indexedWordSkewOrbitCertificate_iterate_rank
   indexedWordSkewOrbitCertificate_iterate_orbit
   indexedWordSkewOrbitCertificate_coordinate_orbit
   indexedWordSkewOrbitCertificate_coordinate_iterate_orbit)

end EvenV11
