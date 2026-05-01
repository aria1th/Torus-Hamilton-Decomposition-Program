import D7Odd.Handoff.PrimeRoot

namespace D7Odd
namespace Handoff
namespace PrimeRoot
namespace PrimeDimension

abbrev SymbolPerm (D : PrimeDimension) :=
  D.Color → D.CanonSym

abbrev CountMatrix (D : PrimeDimension) :=
  D.Color → D.CanonSym → Nat

def rowSum (D : PrimeDimension) (A : D.CountMatrix) (i : D.Color) : Nat :=
  Finset.univ.sum fun j : D.CanonSym => A i j

def colSum (D : PrimeDimension) (A : D.CountMatrix) (j : D.CanonSym) : Nat :=
  Finset.univ.sum fun i : D.Color => A i j

def CountMatrixValid (D : PrimeDimension) (m : Nat) (A : D.CountMatrix) : Prop :=
  (∀ i : D.Color, D.rowSum A i = m) ∧
    (∀ j : D.CanonSym, D.colSum A j = m)

def canonicalRowPrimitive (D : PrimeDimension) (m : Nat)
    (row : D.CanonSym → Nat) : Prop :=
  Nat.Coprime (row D.zero) m ∧
    ∀ k : D.CanonSym, 2 ≤ k.val →
      Nat.Coprime
        (Int.natAbs (Int.ofNat (row k) - Int.ofNat (row D.one))) m

def CountMatrixPrimitive (D : PrimeDimension) (m : Nat)
    (A : D.CountMatrix) : Prop :=
  ∀ c : D.Color, D.canonicalRowPrimitive m (fun sym => A c sym)

def CountMatrixCertified (D : PrimeDimension) (m : Nat)
    (A : D.CountMatrix) : Prop :=
  D.CountMatrixValid m A ∧ D.CountMatrixPrimitive m A

def scheduleCount (D : PrimeDimension) (L : List D.SymbolPerm)
    (c : D.Color) (sym : D.CanonSym) : Nat :=
  L.countP fun σ => σ c == sym

def scheduleListLatin (D : PrimeDimension) (L : List D.SymbolPerm) : Prop :=
  List.Forall Function.Bijective L

def canonicalWord (D : PrimeDimension) (L : List D.SymbolPerm)
    (c : D.Color) : List D.CanonSym :=
  L.map fun σ => σ c

def canonicalWordCount (D : PrimeDimension)
    (W : List D.CanonSym) (sym : D.CanonSym) : Nat :=
  W.countP fun x => x == sym

def CanonicalWordCertified (D : PrimeDimension)
    (m : Nat) (W : List D.CanonSym) : Prop :=
  W.length = m ∧
    D.canonicalRowPrimitive m (fun sym => D.canonicalWordCount W sym)

structure CountMatrixSchedule (D : PrimeDimension) (m : Nat) where
  matrix : D.CountMatrix
  schedule : List D.SymbolPerm
  certified : D.CountMatrixCertified m matrix
  latin : D.scheduleListLatin schedule
  length_eq : schedule.length = m
  count_eq : ∀ c sym, D.scheduleCount schedule c sym = matrix c sym

end PrimeDimension
end PrimeRoot
end Handoff
end D7Odd
