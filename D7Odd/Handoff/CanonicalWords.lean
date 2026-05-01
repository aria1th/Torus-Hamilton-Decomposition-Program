import D7Odd.Handoff.CanonicalSchedules

namespace D7Odd
namespace Handoff

abbrev CanonSym := Fin 7

def canonicalWord (L : List SymbolPerm7) (c : Fin 7) : List CanonSym :=
  L.map fun σ => σ c

def canonicalWordCount (W : List CanonSym) (sym : CanonSym) : Nat :=
  W.countP fun x => x == sym

def CanonicalWordCertified (m : Nat) (W : List CanonSym) : Prop :=
  W.length = m ∧ canonicalRowPrimitive m (fun sym => canonicalWordCount W sym)

theorem CanonicalWordCertified.length_eq {m : Nat} {W : List CanonSym}
    (hW : CanonicalWordCertified m W) :
    W.length = m :=
  hW.1

theorem CanonicalWordCertified.coprime_zero {m : Nat} {W : List CanonSym}
    (hW : CanonicalWordCertified m W) :
    Nat.Coprime (canonicalWordCount W 0) m :=
  hW.2.1

theorem CanonicalWordCertified.coprime_diff {m : Nat} {W : List CanonSym}
    (hW : CanonicalWordCertified m W) (k : Fin 7) (hk : 2 ≤ k.val) :
    Nat.Coprime
      (Int.natAbs (Int.ofNat (canonicalWordCount W k) -
        Int.ofNat (canonicalWordCount W 1))) m :=
  hW.2.2 k hk

theorem canonicalWord_length (L : List SymbolPerm7) (c : Fin 7) :
    (canonicalWord L c).length = L.length := by
  simp [canonicalWord]

theorem canonicalWordCount_of_schedule
    (L : List SymbolPerm7) (c sym : Fin 7) :
    canonicalWordCount (canonicalWord L c) sym = scheduleCount L c sym := by
  simp [canonicalWord, canonicalWordCount, scheduleCount, List.countP_map, Function.comp_def]

theorem countMatrixSchedule_word_certified {m : Nat}
    (P : CountMatrixSchedule m) (c : Fin 7) :
    CanonicalWordCertified m (canonicalWord P.schedule c) := by
  constructor
  · rw [canonicalWord_length, P.length_eq]
  · have hprim := P.certified.2 c
    simpa [canonicalRowPrimitive, canonicalWordCount_of_schedule, P.count_eq] using hprim

def GenericCanonicalWordsCertified (m : Nat) : Prop :=
  ∃ P : CountMatrixSchedule m,
    ∀ c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)

theorem generic_canonical_words_certified {m : Nat}
    (hm7 : 7 ≤ m) (hodd : Odd m) :
    GenericCanonicalWordsCertified m := by
  rcases generic_count_matrix_schedule hm7 hodd with ⟨P⟩
  exact ⟨P, fun c => countMatrixSchedule_word_certified P c⟩

end Handoff
end D7Odd
