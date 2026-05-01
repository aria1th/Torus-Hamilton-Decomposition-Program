import D7Odd.Basic

namespace D7Odd

inductive PrimitiveRow
  | r36
  | r53
  | r65
  | r25
  | r34
  | r56
  | r52
  | r45
  | r63
  | r35
deriving DecidableEq, Repr, Fintype

namespace PrimitiveRow

def row36 : Fin 7 -> Fin 7
  | 0 => 6
  | 1 => 4
  | 2 => 5
  | 3 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 2

def row53 : Fin 7 -> Fin 7
  | 0 => 3
  | 1 => 6
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 5
  | 6 => 4

def row65 : Fin 7 -> Fin 7
  | 0 => 5
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 6

def row25 : Fin 7 -> Fin 7
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 2
  | 4 => 6
  | 5 => 0
  | 6 => 1

def row34 : Fin 7 -> Fin 7
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | 4 => 0
  | 5 => 1
  | 6 => 2

def row56 : Fin 7 -> Fin 7
  | 0 => 6
  | 1 => 5
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 4

def row52 : Fin 7 -> Fin 7
  | 0 => 2
  | 1 => 6
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 3
  | 6 => 4

def row45 : Fin 7 -> Fin 7
  | 0 => 5
  | 1 => 4
  | 2 => 6
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 3

def row63 : Fin 7 -> Fin 7
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 6
  | 5 => 4
  | 6 => 5

def row35 : Fin 7 -> Fin 7
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 6
  | 4 => 0
  | 5 => 1
  | 6 => 2

def row : PrimitiveRow -> Fin 7 -> Fin 7
  | .r36 => row36
  | .r53 => row53
  | .r65 => row65
  | .r25 => row25
  | .r34 => row34
  | .r56 => row56
  | .r52 => row52
  | .r45 => row45
  | .r63 => row63
  | .r35 => row35

theorem row_bijective (r : PrimitiveRow) : Function.Bijective (row r) := by
  cases r <;> decide

theorem row_injective (r : PrimitiveRow) : Function.Injective (row r) :=
  (row_bijective r).1

theorem row_surjective (r : PrimitiveRow) : Function.Surjective (row r) :=
  (row_bijective r).2

end PrimitiveRow

def lambdaC : Fin 7 -> Fin 7
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 0

def lambdaSB : Fin 7 -> Fin 7
  | 0 => 5
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 1
  | 5 => 6
  | 6 => 0

theorem lambdaC_bijective : Function.Bijective lambdaC := by
  decide

theorem lambdaSB_bijective : Function.Bijective lambdaSB := by
  decide

end D7Odd
