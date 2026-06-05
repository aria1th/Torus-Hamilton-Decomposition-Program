import EvenV11.WordSkew

namespace EvenV11
namespace TerminalWords

inductive TerminalSymbol where
  | F0
  | F1
  | F2
  deriving DecidableEq, Repr

def terminalWord4 : List TerminalSymbol :=
  [TerminalSymbol.F1, TerminalSymbol.F0, TerminalSymbol.F0]

def terminalWord6 : List TerminalSymbol :=
  [TerminalSymbol.F1, TerminalSymbol.F1,
   TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0]

def terminalTrace4 : List TerminalSymbol :=
  [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F1]

def terminalTrace6 : List TerminalSymbol :=
  [TerminalSymbol.F0, TerminalSymbol.F0, TerminalSymbol.F0,
   TerminalSymbol.F1, TerminalSymbol.F1]

def terminalResetWord4 : List TerminalSymbol :=
  [TerminalSymbol.F1, TerminalSymbol.F2, TerminalSymbol.F0]

def terminalResetTrace4 : List TerminalSymbol :=
  [TerminalSymbol.F0, TerminalSymbol.F2, TerminalSymbol.F1]

theorem terminalWord4_length :
    terminalWord4.length = 3 := by
  rfl

theorem terminalWord6_length :
    terminalWord6.length = 5 := by
  rfl

theorem terminalTrace4_length :
    terminalTrace4.length = 3 := by
  rfl

theorem terminalTrace6_length :
    terminalTrace6.length = 5 := by
  rfl

theorem terminalResetWord4_length :
    terminalResetWord4.length = 3 := by
  rfl

theorem terminalResetTrace4_length :
    terminalResetTrace4.length = 3 := by
  rfl

theorem terminalWord4_eval
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalWord4 x =
      F TerminalSymbol.F0
        (F TerminalSymbol.F0
          (F TerminalSymbol.F1 x)) := by
  rfl

theorem terminalWord6_eval
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalWord6 x =
      F TerminalSymbol.F0
        (F TerminalSymbol.F0
          (F TerminalSymbol.F0
            (F TerminalSymbol.F1
              (F TerminalSymbol.F1 x)))) := by
  rfl

theorem terminalTrace4_eval
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalTrace4 x =
      F TerminalSymbol.F1
        (F TerminalSymbol.F0
          (F TerminalSymbol.F0 x)) := by
  rfl

theorem terminalTrace6_eval
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalTrace6 x =
      F TerminalSymbol.F1
        (F TerminalSymbol.F1
          (F TerminalSymbol.F0
            (F TerminalSymbol.F0
              (F TerminalSymbol.F0 x)))) := by
  rfl

theorem terminalResetWord4_eval
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalResetWord4 x =
      F TerminalSymbol.F0
        (F TerminalSymbol.F2
          (F TerminalSymbol.F1 x)) := by
  rfl

theorem terminalResetTrace4_eval
    {α : Type*} (F : TerminalSymbol → α → α) (x : α) :
    wordEval F terminalResetTrace4 x =
      F TerminalSymbol.F1
        (F TerminalSymbol.F2
          (F TerminalSymbol.F0 x)) := by
  rfl

end TerminalWords

export TerminalWords
  (TerminalSymbol terminalWord4 terminalWord6 terminalTrace4 terminalTrace6
   terminalResetWord4 terminalResetTrace4
   terminalWord4_length terminalWord6_length terminalTrace4_length
   terminalTrace6_length terminalResetWord4_length
   terminalResetTrace4_length
   terminalWord4_eval terminalWord6_eval terminalTrace4_eval
   terminalTrace6_eval terminalResetWord4_eval terminalResetTrace4_eval)

namespace TerminalSymbol

export TerminalWords.TerminalSymbol (F0 F1 F2)

end TerminalSymbol

end EvenV11
