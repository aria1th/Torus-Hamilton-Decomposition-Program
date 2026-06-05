import EvenV11.FiniteCertificate
import EvenV11.TerminalWords
import EvenV11.UnitCarry

namespace EvenV11
namespace TerminalA2LowMod

abbrev TerminalQ (m : Nat) := ZMod m × ZMod m

theorem terminalQ_card (m : Nat) [NeZero m] :
    Fintype.card (TerminalQ m) = m * m := by
  simp

inductive TerminalRow where
  | default
  | tau02
  | tau12
  | tau01
  | chiPlus
  | chiMinus
  deriving DecidableEq, Repr

def q {m : Nat} (x y : ZMod m) : TerminalQ m :=
  (x, y)

def a0 {m : Nat} : TerminalQ m := q 1 0
def a1 {m : Nat} : TerminalQ m := q 0 1
def a2 {m : Nat} : TerminalQ m := q 0 0

def p {m : Nat} : TerminalQ m := q 1 2
def eH {m : Nat} : TerminalQ m := q 1 0
def eV {m : Nat} : TerminalQ m := q 0 1
def eD {m : Nat} : TerminalQ m := q (-1) 1

def delta0 {m : Nat} : TerminalQ m := q 0 1
def delta1 {m : Nat} : TerminalQ m := q 1 0
def delta2 {m : Nat} : TerminalQ m := q 1 (-1)

def terminalOmega {m : Nat} [NeZero m] (z : TerminalQ m) :
    TerminalRow :=
  if z = p then
    TerminalRow.default
  else if z = p - eH then
    TerminalRow.chiMinus
  else if z = p + eH then
    TerminalRow.chiPlus
  else if z = p - eV then
    TerminalRow.chiPlus
  else if z = p + eV then
    TerminalRow.chiMinus
  else if z = p - eD then
    TerminalRow.chiMinus
  else if z = p + eD then
    TerminalRow.chiPlus
  else if z.2 = (2 : ZMod m) then
    TerminalRow.tau02
  else if z.1 = (1 : ZMod m) then
    TerminalRow.tau12
  else if z.1 + z.2 = (3 : ZMod m) then
    TerminalRow.tau01
  else
    TerminalRow.default

def terminalTarget0 {m : Nat} : TerminalRow → TerminalQ m
  | TerminalRow.default => a0
  | TerminalRow.tau02 => a2
  | TerminalRow.tau12 => a0
  | TerminalRow.tau01 => a1
  | TerminalRow.chiPlus => a1
  | TerminalRow.chiMinus => a2

def terminalTarget1 {m : Nat} : TerminalRow → TerminalQ m
  | TerminalRow.default => a1
  | TerminalRow.tau02 => a1
  | TerminalRow.tau12 => a2
  | TerminalRow.tau01 => a0
  | TerminalRow.chiPlus => a2
  | TerminalRow.chiMinus => a0

def terminalTarget2 {m : Nat} : TerminalRow → TerminalQ m
  | TerminalRow.default => a2
  | TerminalRow.tau02 => a0
  | TerminalRow.tau12 => a1
  | TerminalRow.tau01 => a2
  | TerminalRow.chiPlus => a0
  | TerminalRow.chiMinus => a1

/-- The vertex `a_i` of the elementary A2 triangle. -/
def terminalVertex {m : Nat} : Fin 3 → TerminalQ m
  | 0 => a0
  | 1 => a1
  | 2 => a2

/-- The row word as a map on target indices. The six cases are the paper's
`012`, `210`, `021`, `102`, `120`, and `201`. -/
def terminalRowTargetIndex : TerminalRow → Fin 3 → Fin 3
  | TerminalRow.default, i => i
  | TerminalRow.tau02, 0 => 2
  | TerminalRow.tau02, 1 => 1
  | TerminalRow.tau02, 2 => 0
  | TerminalRow.tau12, 0 => 0
  | TerminalRow.tau12, 1 => 2
  | TerminalRow.tau12, 2 => 1
  | TerminalRow.tau01, 0 => 1
  | TerminalRow.tau01, 1 => 0
  | TerminalRow.tau01, 2 => 2
  | TerminalRow.chiPlus, 0 => 1
  | TerminalRow.chiPlus, 1 => 2
  | TerminalRow.chiPlus, 2 => 0
  | TerminalRow.chiMinus, 0 => 2
  | TerminalRow.chiMinus, 1 => 0
  | TerminalRow.chiMinus, 2 => 1

/-- Inverse row word on target indices. -/
def terminalRowSourceIndex : TerminalRow → Fin 3 → Fin 3
  | TerminalRow.default, i => i
  | TerminalRow.tau02, 0 => 2
  | TerminalRow.tau02, 1 => 1
  | TerminalRow.tau02, 2 => 0
  | TerminalRow.tau12, 0 => 0
  | TerminalRow.tau12, 1 => 2
  | TerminalRow.tau12, 2 => 1
  | TerminalRow.tau01, 0 => 1
  | TerminalRow.tau01, 1 => 0
  | TerminalRow.tau01, 2 => 2
  | TerminalRow.chiPlus, 0 => 2
  | TerminalRow.chiPlus, 1 => 0
  | TerminalRow.chiPlus, 2 => 1
  | TerminalRow.chiMinus, 0 => 1
  | TerminalRow.chiMinus, 1 => 2
  | TerminalRow.chiMinus, 2 => 0

/-- The terminal row word as a genuine Latin row permutation. -/
def terminalRowEquiv (row : TerminalRow) : Fin 3 ≃ Fin 3 where
  toFun := terminalRowTargetIndex row
  invFun := terminalRowSourceIndex row
  left_inv := by
    intro i
    cases row <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    cases row <;> fin_cases i <;> rfl

theorem terminalTarget0_eq_terminalVertex {m : Nat} (row : TerminalRow) :
    terminalTarget0 (m := m) row =
      terminalVertex (terminalRowEquiv row 0) := by
  cases row <;> rfl

theorem terminalTarget1_eq_terminalVertex {m : Nat} (row : TerminalRow) :
    terminalTarget1 (m := m) row =
      terminalVertex (terminalRowEquiv row 1) := by
  cases row <;> rfl

theorem terminalTarget2_eq_terminalVertex {m : Nat} (row : TerminalRow) :
    terminalTarget2 (m := m) row =
      terminalVertex (terminalRowEquiv row 2) := by
  cases row <;> rfl

theorem terminalTarget_eq_terminalVertex {m : Nat} (row : TerminalRow)
    (i : Fin 3) :
    (match i with
      | 0 => terminalTarget0 (m := m) row
      | 1 => terminalTarget1 (m := m) row
      | 2 => terminalTarget2 (m := m) row) =
    terminalVertex (m := m) (terminalRowEquiv row i) := by
  fin_cases i
  · exact terminalTarget0_eq_terminalVertex row
  · exact terminalTarget1_eq_terminalVertex row
  · exact terminalTarget2_eq_terminalVertex row

/-- The straight-fiber advance `Delta_i` from the paper, indexed by color. -/
def terminalDelta {m : Nat} : Fin 3 → TerminalQ m
  | 0 => delta0
  | 1 => delta1
  | 2 => delta2

/-- Terminal symbols indexed by the three terminal colors. -/
def terminalSymbolOfIndex : Fin 3 → TerminalSymbol
  | 0 => TerminalSymbol.F0
  | 1 => TerminalSymbol.F1
  | 2 => TerminalSymbol.F2

/-- The paper's local terminal jump
`eta_i(z) = (z-a_i) + a_{omega(z-a_i)_i}`, indexed by terminal color. -/
def terminalEta {m : Nat} [NeZero m] (i : Fin 3) (z : TerminalQ m) :
    TerminalQ m :=
  (z - terminalVertex (m := m) i) +
    terminalVertex (m := m)
      (terminalRowEquiv (terminalOmega (z - terminalVertex (m := m) i)) i)

/-- The run-collapsed terminal return `F_i(z) = eta_i(z + Delta_i)`,
indexed by terminal color. -/
def terminalReturn {m : Nat} [NeZero m] (i : Fin 3) (z : TerminalQ m) :
    TerminalQ m :=
  terminalEta i (z + terminalDelta i)

def terminalEta0 {m : Nat} [NeZero m] (z : TerminalQ m) :
    TerminalQ m :=
  (z - a0) + terminalTarget0 (terminalOmega (z - a0))

def terminalEta1 {m : Nat} [NeZero m] (z : TerminalQ m) :
    TerminalQ m :=
  (z - a1) + terminalTarget1 (terminalOmega (z - a1))

def terminalEta2 {m : Nat} [NeZero m] (z : TerminalQ m) :
    TerminalQ m :=
  (z - a2) + terminalTarget2 (terminalOmega (z - a2))

def terminalReturn0 {m : Nat} [NeZero m] (z : TerminalQ m) :
    TerminalQ m :=
  terminalEta0 (z + delta0)

def terminalReturn1 {m : Nat} [NeZero m] (z : TerminalQ m) :
    TerminalQ m :=
  terminalEta1 (z + delta1)

def terminalReturn2 {m : Nat} [NeZero m] (z : TerminalQ m) :
    TerminalQ m :=
  terminalEta2 (z + delta2)

@[simp] theorem terminalEta_zero {m : Nat} [NeZero m] (z : TerminalQ m) :
    terminalEta (m := m) 0 z = terminalEta0 z := by
  simp [terminalEta, terminalEta0, terminalVertex,
    terminalTarget0_eq_terminalVertex]

@[simp] theorem terminalEta_one {m : Nat} [NeZero m] (z : TerminalQ m) :
    terminalEta (m := m) 1 z = terminalEta1 z := by
  simp [terminalEta, terminalEta1, terminalVertex,
    terminalTarget1_eq_terminalVertex]

@[simp] theorem terminalEta_two {m : Nat} [NeZero m] (z : TerminalQ m) :
    terminalEta (m := m) 2 z = terminalEta2 z := by
  simp [terminalEta, terminalEta2, terminalVertex,
    terminalTarget2_eq_terminalVertex]

@[simp] theorem terminalReturn_zero {m : Nat} [NeZero m] (z : TerminalQ m) :
    terminalReturn (m := m) 0 z = terminalReturn0 z := by
  simp [terminalReturn, terminalDelta, terminalReturn0]

@[simp] theorem terminalReturn_one {m : Nat} [NeZero m] (z : TerminalQ m) :
    terminalReturn (m := m) 1 z = terminalReturn1 z := by
  simp [terminalReturn, terminalDelta, terminalReturn1]

@[simp] theorem terminalReturn_two {m : Nat} [NeZero m] (z : TerminalQ m) :
    terminalReturn (m := m) 2 z = terminalReturn2 z := by
  simp [terminalReturn, terminalDelta, terminalReturn2]

def terminalSymbolStep (m : Nat) [NeZero m] :
    TerminalSymbol → TerminalQ m → TerminalQ m
  | TerminalSymbol.F0 => terminalReturn0
  | TerminalSymbol.F1 => terminalReturn1
  | TerminalSymbol.F2 => terminalReturn2

theorem terminalSymbolStep_of_index {m : Nat} [NeZero m] (i : Fin 3) :
    terminalSymbolStep m (terminalSymbolOfIndex i) = terminalReturn i := by
  funext z
  fin_cases i <;> simp [terminalSymbolOfIndex, terminalSymbolStep]

def q4 (x y : Nat) : TerminalQ 4 :=
  q (x : ZMod 4) (y : ZMod 4)

def q6 (x y : Nat) : TerminalQ 6 :=
  q (x : ZMod 6) (y : ZMod 6)

def terminalOrbit4 : Fin 16 → TerminalQ 4 := fun i =>
  match i.val with
  | 0 => q4 0 0
  | 1 => q4 0 2
  | 2 => q4 0 1
  | 3 => q4 1 2
  | 4 => q4 1 0
  | 5 => q4 1 1
  | 6 => q4 1 3
  | 7 => q4 2 1
  | 8 => q4 2 2
  | 9 => q4 2 0
  | 10 => q4 2 3
  | 11 => q4 3 1
  | 12 => q4 3 0
  | 13 => q4 3 2
  | 14 => q4 0 3
  | _ => q4 3 3

def terminalOrbit6 : Fin 36 → TerminalQ 6 := fun i =>
  match i.val with
  | 0 => q6 0 0
  | 1 => q6 3 1
  | 2 => q6 4 5
  | 3 => q6 4 4
  | 4 => q6 4 3
  | 5 => q6 5 1
  | 6 => q6 0 3
  | 7 => q6 1 0
  | 8 => q6 2 2
  | 9 => q6 3 5
  | 10 => q6 4 2
  | 11 => q6 2 3
  | 12 => q6 5 5
  | 13 => q6 0 2
  | 14 => q6 1 5
  | 15 => q6 2 1
  | 16 => q6 3 4
  | 17 => q6 5 0
  | 18 => q6 1 2
  | 19 => q6 2 5
  | 20 => q6 3 3
  | 21 => q6 0 5
  | 22 => q6 1 1
  | 23 => q6 1 4
  | 24 => q6 4 0
  | 25 => q6 5 3
  | 26 => q6 0 1
  | 27 => q6 1 3
  | 28 => q6 3 0
  | 29 => q6 3 2
  | 30 => q6 0 4
  | 31 => q6 2 0
  | 32 => q6 2 4
  | 33 => q6 4 1
  | 34 => q6 5 4
  | _ => q6 5 2

theorem terminalOrbit4_bijective :
    Function.Bijective terminalOrbit4 := by
  decide

theorem terminalOrbit6_bijective :
    Function.Bijective terminalOrbit6 := by
  decide

noncomputable def terminalOrbit4Equiv : Fin 16 ≃ TerminalQ 4 :=
  Equiv.ofBijective terminalOrbit4 terminalOrbit4_bijective

noncomputable def terminalOrbit6Equiv : Fin 36 ≃ TerminalQ 6 :=
  Equiv.ofBijective terminalOrbit6 terminalOrbit6_bijective

theorem terminalTrace4_stepOrbit_raw :
    ∀ i : Fin 16,
      terminalOrbit4 (i + 1) =
        wordEval (terminalSymbolStep 4) EvenV11.terminalTrace4
          (terminalOrbit4 i) := by
  decide

theorem terminalTrace6_stepOrbit_raw :
    ∀ i : Fin 36,
      terminalOrbit6 (i + 1) =
        wordEval (terminalSymbolStep 6) EvenV11.terminalTrace6
          (terminalOrbit6 i) := by
  decide

theorem terminalTrace4_stepOrbit :
    ∀ i : Fin 16,
      terminalOrbit4Equiv (i + 1) =
        wordEval (terminalSymbolStep 4) EvenV11.terminalTrace4
          (terminalOrbit4Equiv i) := by
  simpa [terminalOrbit4Equiv] using terminalTrace4_stepOrbit_raw

theorem terminalTrace6_stepOrbit :
    ∀ i : Fin 36,
      terminalOrbit6Equiv (i + 1) =
        wordEval (terminalSymbolStep 6) EvenV11.terminalTrace6
          (terminalOrbit6Equiv i) := by
  simpa [terminalOrbit6Equiv] using terminalTrace6_stepOrbit_raw

noncomputable def terminalTrace4Certificate :
    IndexedWordOrbitCertificate TerminalSymbol (TerminalQ 4) 16 where
  symbolStep := terminalSymbolStep 4
  word := EvenV11.terminalTrace4
  orbit := terminalOrbit4Equiv
  stepOrbit := terminalTrace4_stepOrbit

noncomputable def terminalTrace6Certificate :
    IndexedWordOrbitCertificate TerminalSymbol (TerminalQ 6) 36 where
  symbolStep := terminalSymbolStep 6
  word := EvenV11.terminalTrace6
  orbit := terminalOrbit6Equiv
  stepOrbit := terminalTrace6_stepOrbit

theorem terminalTrace4_singleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) EvenV11.terminalTrace4) := by
  simpa [terminalTrace4Certificate] using
    indexedWordOrbitCertificate_singleCycle terminalTrace4Certificate

theorem terminalTrace4_iterate_orbit
    (i : Fin 16) :
    ∀ n : Nat,
      ((wordEval (terminalSymbolStep 4) EvenV11.terminalTrace4)^[n])
          (terminalOrbit4Equiv i) =
        terminalOrbit4Equiv (i + Fin.ofNat 16 n) := by
  simpa [terminalTrace4Certificate] using
    indexedWordOrbitCertificate_iterate_orbit terminalTrace4Certificate i

theorem terminalTrace4_coordinate_orbit
    (i : Fin 16) :
    terminalOrbit4Equiv.symm (terminalOrbit4Equiv i) = i := by
  simp

theorem terminalTrace4_coordinate_iterate_orbit
    (i : Fin 16) (n : Nat) :
    terminalOrbit4Equiv.symm
        (((wordEval (terminalSymbolStep 4) EvenV11.terminalTrace4)^[n])
          (terminalOrbit4Equiv i)) =
      i + Fin.ofNat 16 n := by
  simpa [terminalTrace4Certificate] using
    indexedWordOrbitCertificate_coordinate_iterate_orbit
      terminalTrace4Certificate i n

theorem terminalTrace6_singleCycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) EvenV11.terminalTrace6) := by
  simpa [terminalTrace6Certificate] using
    indexedWordOrbitCertificate_singleCycle terminalTrace6Certificate

theorem terminalQ_complementExponentSum
    {m M : Nat} [NeZero m] (q0 : TerminalQ m) :
    (∑ q : TerminalQ m, if q = q0 then (0 : ZMod M) else 1) =
      ((m * m - 1 : Nat) : ZMod M) := by
  rw [complementSingletonExponentSum, terminalQ_card]

theorem terminalQComplementProductExponentSingleCycle
    {N m k : Nat} [NeZero N] [NeZero m]
    (terminalStep : TerminalQ m → TerminalQ m)
    (terminalRank : TerminalQ m ≃ ZMod N)
    (base q0 : TerminalQ m)
    (hstep : ∀ q : TerminalQ m,
      terminalRank (terminalStep q) = terminalRank q + 1) :
    Shared.IsSingleCycleMap
      (productExponentMap terminalStep
        (fun q : TerminalQ m =>
          if q = q0 then (0 : ZMod (m ^ k)) else 1)) :=
  complementSingletonSquareProductExponentSingleCycle terminalStep
    terminalRank base q0 hstep (terminalQ_card m)

end TerminalA2LowMod

export TerminalA2LowMod
  (TerminalQ terminalQ_card TerminalRow terminalOmega terminalReturn0 terminalReturn1
   terminalReturn2 terminalDelta terminalSymbolOfIndex terminalEta terminalReturn
   terminalEta_zero terminalEta_one terminalEta_two terminalReturn_zero
   terminalReturn_one terminalReturn_two terminalVertex terminalRowTargetIndex
   terminalRowSourceIndex
   terminalRowEquiv terminalTarget0_eq_terminalVertex
   terminalTarget1_eq_terminalVertex terminalTarget2_eq_terminalVertex
   terminalTarget_eq_terminalVertex terminalSymbolStep terminalSymbolStep_of_index
   terminalOrbit4 terminalOrbit6
   terminalOrbit4_bijective terminalOrbit4Equiv terminalTrace4_stepOrbit
   terminalTrace4Certificate terminalTrace6Certificate
   terminalTrace4_iterate_orbit terminalTrace4_coordinate_orbit
   terminalTrace4_coordinate_iterate_orbit
   terminalTrace4_singleCycle terminalTrace6_singleCycle
   terminalQ_complementExponentSum
   terminalQComplementProductExponentSingleCycle)

end EvenV11
