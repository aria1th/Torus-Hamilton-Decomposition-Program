import Shared.TorusCayley

set_option linter.style.nativeDecide false

namespace EvenV11
namespace D3EvenM4

abbrev Vertex4 := Shared.TorusVertex 3 4

def dirOfNat (n : Nat) : Shared.TorusDirection 3 :=
  ⟨n % 3, Nat.mod_lt n (by decide)⟩

def point (a b c : Nat) : Vertex4
  | ⟨0, _⟩ => (a : ZMod 4)
  | ⟨1, _⟩ => (b : ZMod 4)
  | ⟨2, _⟩ => (c : ZMod 4)
  | ⟨n + 3, h⟩ => by omega

def dirWordNat (x : Vertex4) : Nat × Nat × Nat :=
  match (x 0).val, (x 1).val, (x 2).val with
  | 0, 0, 0 => (2, 1, 0)
  | 0, 0, 1 => (0, 1, 2)
  | 0, 0, 2 => (1, 2, 0)
  | 0, 0, 3 => (0, 2, 1)
  | 0, 1, 0 => (2, 0, 1)
  | 0, 1, 1 => (0, 2, 1)
  | 0, 1, 2 => (1, 2, 0)
  | 0, 1, 3 => (2, 1, 0)
  | 0, 2, 0 => (1, 2, 0)
  | 0, 2, 1 => (0, 1, 2)
  | 0, 2, 2 => (2, 0, 1)
  | 0, 2, 3 => (2, 1, 0)
  | 0, 3, 0 => (2, 0, 1)
  | 0, 3, 1 => (2, 0, 1)
  | 0, 3, 2 => (2, 1, 0)
  | 0, 3, 3 => (1, 0, 2)
  | 1, 0, 0 => (1, 2, 0)
  | 1, 0, 1 => (2, 1, 0)
  | 1, 0, 2 => (1, 2, 0)
  | 1, 0, 3 => (2, 1, 0)
  | 1, 1, 0 => (1, 0, 2)
  | 1, 1, 1 => (0, 2, 1)
  | 1, 1, 2 => (2, 0, 1)
  | 1, 1, 3 => (0, 1, 2)
  | 1, 2, 0 => (0, 2, 1)
  | 1, 2, 1 => (2, 0, 1)
  | 1, 2, 2 => (2, 1, 0)
  | 1, 2, 3 => (1, 2, 0)
  | 1, 3, 0 => (2, 1, 0)
  | 1, 3, 1 => (2, 0, 1)
  | 1, 3, 2 => (0, 1, 2)
  | 1, 3, 3 => (2, 0, 1)
  | 2, 0, 0 => (0, 2, 1)
  | 2, 0, 1 => (2, 1, 0)
  | 2, 0, 2 => (2, 0, 1)
  | 2, 0, 3 => (0, 2, 1)
  | 2, 1, 0 => (0, 1, 2)
  | 2, 1, 1 => (2, 0, 1)
  | 2, 1, 2 => (1, 2, 0)
  | 2, 1, 3 => (2, 1, 0)
  | 2, 2, 0 => (2, 1, 0)
  | 2, 2, 1 => (1, 2, 0)
  | 2, 2, 2 => (2, 1, 0)
  | 2, 2, 3 => (1, 0, 2)
  | 2, 3, 0 => (1, 0, 2)
  | 2, 3, 1 => (1, 0, 2)
  | 2, 3, 2 => (0, 1, 2)
  | 2, 3, 3 => (2, 1, 0)
  | 3, 0, 0 => (0, 2, 1)
  | 3, 0, 1 => (2, 0, 1)
  | 3, 0, 2 => (0, 1, 2)
  | 3, 0, 3 => (1, 2, 0)
  | 3, 1, 0 => (2, 1, 0)
  | 3, 1, 1 => (2, 1, 0)
  | 3, 1, 2 => (1, 2, 0)
  | 3, 1, 3 => (0, 2, 1)
  | 3, 2, 0 => (2, 0, 1)
  | 3, 2, 1 => (0, 2, 1)
  | 3, 2, 2 => (2, 0, 1)
  | 3, 2, 3 => (2, 1, 0)
  | 3, 3, 0 => (2, 0, 1)
  | 3, 3, 1 => (1, 2, 0)
  | 3, 3, 2 => (2, 0, 1)
  | 3, 3, 3 => (2, 1, 0)
  | _, _, _ => (0, 1, 2)

def colorDir : Shared.TorusColor 3 → Vertex4 → Shared.TorusDirection 3
  | ⟨0, _⟩, x => dirOfNat (dirWordNat x).1
  | ⟨1, _⟩, x => dirOfNat (dirWordNat x).2.1
  | ⟨2, _⟩, x => dirOfNat (dirWordNat x).2.2
  | ⟨n + 3, h⟩, _ => by omega

theorem dirWordNat_perm (x : Vertex4) :
    dirWordNat x = (0, 1, 2) ∨
    dirWordNat x = (0, 2, 1) ∨
    dirWordNat x = (1, 0, 2) ∨
    dirWordNat x = (1, 2, 0) ∨
    dirWordNat x = (2, 0, 1) ∨
    dirWordNat x = (2, 1, 0) := by
  unfold dirWordNat
  split <;> simp

def rank0Nat (x : Vertex4) : Nat :=
  match (x 0).val, (x 1).val, (x 2).val with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 0, 2 => 30
  | 0, 0, 3 => 39
  | 0, 1, 0 => 53
  | 0, 1, 1 => 54
  | 0, 1, 2 => 31
  | 0, 1, 3 => 52
  | 0, 2, 0 => 34
  | 0, 2, 1 => 15
  | 0, 2, 2 => 32
  | 0, 2, 3 => 33
  | 0, 3, 0 => 35
  | 0, 3, 1 => 36
  | 0, 3, 2 => 37
  | 0, 3, 3 => 38
  | 1, 0, 0 => 41
  | 1, 0, 1 => 2
  | 1, 0, 2 => 3
  | 1, 0, 3 => 40
  | 1, 1, 0 => 42
  | 1, 1, 1 => 55
  | 1, 1, 2 => 4
  | 1, 1, 3 => 5
  | 1, 2, 0 => 43
  | 1, 2, 1 => 16
  | 1, 2, 2 => 17
  | 1, 2, 3 => 18
  | 1, 3, 0 => 20
  | 1, 3, 1 => 21
  | 1, 3, 2 => 22
  | 1, 3, 3 => 19
  | 2, 0, 0 => 62
  | 2, 0, 1 => 47
  | 2, 0, 2 => 48
  | 2, 0, 3 => 49
  | 2, 1, 0 => 7
  | 2, 1, 1 => 56
  | 2, 1, 2 => 57
  | 2, 1, 3 => 6
  | 2, 2, 0 => 44
  | 2, 2, 1 => 45
  | 2, 2, 2 => 58
  | 2, 2, 3 => 59
  | 2, 3, 0 => 61
  | 2, 3, 1 => 46
  | 2, 3, 2 => 23
  | 2, 3, 3 => 60
  | 3, 0, 0 => 63
  | 3, 0, 1 => 28
  | 3, 0, 2 => 29
  | 3, 0, 3 => 50
  | 3, 1, 0 => 8
  | 3, 1, 1 => 9
  | 3, 1, 2 => 10
  | 3, 1, 3 => 51
  | 3, 2, 0 => 13
  | 3, 2, 1 => 14
  | 3, 2, 2 => 11
  | 3, 2, 3 => 12
  | 3, 3, 0 => 26
  | 3, 3, 1 => 27
  | 3, 3, 2 => 24
  | 3, 3, 3 => 25
  | _, _, _ => 0

def rank1Nat (x : Vertex4) : Nat :=
  match (x 0).val, (x 1).val, (x 2).val with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 21
  | 0, 0, 2 => 62
  | 0, 0, 3 => 63
  | 0, 1, 0 => 1
  | 0, 1, 1 => 22
  | 0, 1, 2 => 23
  | 0, 1, 3 => 24
  | 0, 2, 0 => 54
  | 0, 2, 1 => 55
  | 0, 2, 2 => 36
  | 0, 2, 3 => 25
  | 0, 3, 0 => 7
  | 0, 3, 1 => 56
  | 0, 3, 2 => 61
  | 0, 3, 3 => 26
  | 1, 0, 0 => 9
  | 1, 0, 1 => 10
  | 1, 0, 2 => 39
  | 1, 0, 3 => 40
  | 1, 1, 0 => 2
  | 1, 1, 1 => 11
  | 1, 1, 2 => 12
  | 1, 1, 3 => 41
  | 1, 2, 0 => 43
  | 1, 2, 1 => 44
  | 1, 2, 2 => 37
  | 1, 2, 3 => 42
  | 1, 3, 0 => 8
  | 1, 3, 1 => 57
  | 1, 3, 2 => 38
  | 1, 3, 3 => 27
  | 2, 0, 0 => 30
  | 2, 0, 1 => 31
  | 2, 0, 2 => 48
  | 2, 0, 3 => 29
  | 2, 1, 0 => 3
  | 2, 1, 1 => 32
  | 2, 1, 2 => 13
  | 2, 1, 3 => 14
  | 2, 2, 0 => 4
  | 2, 2, 1 => 45
  | 2, 2, 2 => 46
  | 2, 2, 3 => 15
  | 2, 3, 0 => 5
  | 2, 3, 1 => 58
  | 2, 3, 2 => 47
  | 2, 3, 3 => 28
  | 3, 0, 0 => 19
  | 3, 0, 1 => 20
  | 3, 0, 2 => 49
  | 3, 0, 3 => 18
  | 3, 1, 0 => 52
  | 3, 1, 1 => 33
  | 3, 1, 2 => 50
  | 3, 1, 3 => 51
  | 3, 2, 0 => 53
  | 3, 2, 1 => 34
  | 3, 2, 2 => 35
  | 3, 2, 3 => 16
  | 3, 3, 0 => 6
  | 3, 3, 1 => 59
  | 3, 3, 2 => 60
  | 3, 3, 3 => 17
  | _, _, _ => 0

def rank2Nat (x : Vertex4) : Nat :=
  match (x 0).val, (x 1).val, (x 2).val with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 9
  | 0, 0, 2 => 10
  | 0, 0, 3 => 23
  | 0, 1, 0 => 53
  | 0, 1, 1 => 34
  | 0, 1, 2 => 15
  | 0, 1, 3 => 24
  | 0, 2, 0 => 54
  | 0, 2, 1 => 35
  | 0, 2, 2 => 36
  | 0, 2, 3 => 45
  | 0, 3, 0 => 63
  | 0, 3, 1 => 8
  | 0, 3, 2 => 37
  | 0, 3, 3 => 62
  | 1, 0, 0 => 1
  | 1, 0, 1 => 30
  | 1, 0, 2 => 11
  | 1, 0, 3 => 40
  | 1, 1, 0 => 26
  | 1, 1, 1 => 27
  | 1, 1, 2 => 16
  | 1, 1, 3 => 25
  | 1, 2, 0 => 55
  | 1, 2, 1 => 28
  | 1, 2, 2 => 17
  | 1, 2, 3 => 46
  | 1, 3, 0 => 56
  | 1, 3, 1 => 29
  | 1, 3, 2 => 38
  | 1, 3, 3 => 39
  | 2, 0, 0 => 2
  | 2, 0, 1 => 31
  | 2, 0, 2 => 12
  | 2, 0, 3 => 41
  | 2, 1, 0 => 3
  | 2, 1, 1 => 4
  | 2, 1, 2 => 13
  | 2, 1, 3 => 42
  | 2, 2, 0 => 48
  | 2, 2, 1 => 5
  | 2, 2, 2 => 18
  | 2, 2, 3 => 47
  | 2, 3, 0 => 57
  | 2, 3, 1 => 58
  | 2, 3, 2 => 59
  | 2, 3, 3 => 60
  | 3, 0, 0 => 51
  | 3, 0, 1 => 32
  | 3, 0, 2 => 21
  | 3, 0, 3 => 22
  | 3, 1, 0 => 52
  | 3, 1, 1 => 33
  | 3, 1, 2 => 14
  | 3, 1, 3 => 43
  | 3, 2, 0 => 49
  | 3, 2, 1 => 6
  | 3, 2, 2 => 19
  | 3, 2, 3 => 44
  | 3, 3, 0 => 50
  | 3, 3, 1 => 7
  | 3, 3, 2 => 20
  | 3, 3, 3 => 61
  | _, _, _ => 0

def rank0Fin (x : Vertex4) : Fin 64 :=
  ⟨rank0Nat x % 64, Nat.mod_lt _ (by decide)⟩

def rank1Fin (x : Vertex4) : Fin 64 :=
  ⟨rank1Nat x % 64, Nat.mod_lt _ (by decide)⟩

def rank2Fin (x : Vertex4) : Fin 64 :=
  ⟨rank2Nat x % 64, Nat.mod_lt _ (by decide)⟩

def cycle0 (i : Fin 64) : Vertex4 :=
  match i with
  | ⟨0, _⟩ => point 0 0 0
  | ⟨1, _⟩ => point 0 0 1
  | ⟨2, _⟩ => point 1 0 1
  | ⟨3, _⟩ => point 1 0 2
  | ⟨4, _⟩ => point 1 1 2
  | ⟨5, _⟩ => point 1 1 3
  | ⟨6, _⟩ => point 2 1 3
  | ⟨7, _⟩ => point 2 1 0
  | ⟨8, _⟩ => point 3 1 0
  | ⟨9, _⟩ => point 3 1 1
  | ⟨10, _⟩ => point 3 1 2
  | ⟨11, _⟩ => point 3 2 2
  | ⟨12, _⟩ => point 3 2 3
  | ⟨13, _⟩ => point 3 2 0
  | ⟨14, _⟩ => point 3 2 1
  | ⟨15, _⟩ => point 0 2 1
  | ⟨16, _⟩ => point 1 2 1
  | ⟨17, _⟩ => point 1 2 2
  | ⟨18, _⟩ => point 1 2 3
  | ⟨19, _⟩ => point 1 3 3
  | ⟨20, _⟩ => point 1 3 0
  | ⟨21, _⟩ => point 1 3 1
  | ⟨22, _⟩ => point 1 3 2
  | ⟨23, _⟩ => point 2 3 2
  | ⟨24, _⟩ => point 3 3 2
  | ⟨25, _⟩ => point 3 3 3
  | ⟨26, _⟩ => point 3 3 0
  | ⟨27, _⟩ => point 3 3 1
  | ⟨28, _⟩ => point 3 0 1
  | ⟨29, _⟩ => point 3 0 2
  | ⟨30, _⟩ => point 0 0 2
  | ⟨31, _⟩ => point 0 1 2
  | ⟨32, _⟩ => point 0 2 2
  | ⟨33, _⟩ => point 0 2 3
  | ⟨34, _⟩ => point 0 2 0
  | ⟨35, _⟩ => point 0 3 0
  | ⟨36, _⟩ => point 0 3 1
  | ⟨37, _⟩ => point 0 3 2
  | ⟨38, _⟩ => point 0 3 3
  | ⟨39, _⟩ => point 0 0 3
  | ⟨40, _⟩ => point 1 0 3
  | ⟨41, _⟩ => point 1 0 0
  | ⟨42, _⟩ => point 1 1 0
  | ⟨43, _⟩ => point 1 2 0
  | ⟨44, _⟩ => point 2 2 0
  | ⟨45, _⟩ => point 2 2 1
  | ⟨46, _⟩ => point 2 3 1
  | ⟨47, _⟩ => point 2 0 1
  | ⟨48, _⟩ => point 2 0 2
  | ⟨49, _⟩ => point 2 0 3
  | ⟨50, _⟩ => point 3 0 3
  | ⟨51, _⟩ => point 3 1 3
  | ⟨52, _⟩ => point 0 1 3
  | ⟨53, _⟩ => point 0 1 0
  | ⟨54, _⟩ => point 0 1 1
  | ⟨55, _⟩ => point 1 1 1
  | ⟨56, _⟩ => point 2 1 1
  | ⟨57, _⟩ => point 2 1 2
  | ⟨58, _⟩ => point 2 2 2
  | ⟨59, _⟩ => point 2 2 3
  | ⟨60, _⟩ => point 2 3 3
  | ⟨61, _⟩ => point 2 3 0
  | ⟨62, _⟩ => point 2 0 0
  | ⟨63, _⟩ => point 3 0 0
  | ⟨n + 64, h⟩ => by omega

def cycle1 (i : Fin 64) : Vertex4 :=
  match i with
  | ⟨0, _⟩ => point 0 0 0
  | ⟨1, _⟩ => point 0 1 0
  | ⟨2, _⟩ => point 1 1 0
  | ⟨3, _⟩ => point 2 1 0
  | ⟨4, _⟩ => point 2 2 0
  | ⟨5, _⟩ => point 2 3 0
  | ⟨6, _⟩ => point 3 3 0
  | ⟨7, _⟩ => point 0 3 0
  | ⟨8, _⟩ => point 1 3 0
  | ⟨9, _⟩ => point 1 0 0
  | ⟨10, _⟩ => point 1 0 1
  | ⟨11, _⟩ => point 1 1 1
  | ⟨12, _⟩ => point 1 1 2
  | ⟨13, _⟩ => point 2 1 2
  | ⟨14, _⟩ => point 2 1 3
  | ⟨15, _⟩ => point 2 2 3
  | ⟨16, _⟩ => point 3 2 3
  | ⟨17, _⟩ => point 3 3 3
  | ⟨18, _⟩ => point 3 0 3
  | ⟨19, _⟩ => point 3 0 0
  | ⟨20, _⟩ => point 3 0 1
  | ⟨21, _⟩ => point 0 0 1
  | ⟨22, _⟩ => point 0 1 1
  | ⟨23, _⟩ => point 0 1 2
  | ⟨24, _⟩ => point 0 1 3
  | ⟨25, _⟩ => point 0 2 3
  | ⟨26, _⟩ => point 0 3 3
  | ⟨27, _⟩ => point 1 3 3
  | ⟨28, _⟩ => point 2 3 3
  | ⟨29, _⟩ => point 2 0 3
  | ⟨30, _⟩ => point 2 0 0
  | ⟨31, _⟩ => point 2 0 1
  | ⟨32, _⟩ => point 2 1 1
  | ⟨33, _⟩ => point 3 1 1
  | ⟨34, _⟩ => point 3 2 1
  | ⟨35, _⟩ => point 3 2 2
  | ⟨36, _⟩ => point 0 2 2
  | ⟨37, _⟩ => point 1 2 2
  | ⟨38, _⟩ => point 1 3 2
  | ⟨39, _⟩ => point 1 0 2
  | ⟨40, _⟩ => point 1 0 3
  | ⟨41, _⟩ => point 1 1 3
  | ⟨42, _⟩ => point 1 2 3
  | ⟨43, _⟩ => point 1 2 0
  | ⟨44, _⟩ => point 1 2 1
  | ⟨45, _⟩ => point 2 2 1
  | ⟨46, _⟩ => point 2 2 2
  | ⟨47, _⟩ => point 2 3 2
  | ⟨48, _⟩ => point 2 0 2
  | ⟨49, _⟩ => point 3 0 2
  | ⟨50, _⟩ => point 3 1 2
  | ⟨51, _⟩ => point 3 1 3
  | ⟨52, _⟩ => point 3 1 0
  | ⟨53, _⟩ => point 3 2 0
  | ⟨54, _⟩ => point 0 2 0
  | ⟨55, _⟩ => point 0 2 1
  | ⟨56, _⟩ => point 0 3 1
  | ⟨57, _⟩ => point 1 3 1
  | ⟨58, _⟩ => point 2 3 1
  | ⟨59, _⟩ => point 3 3 1
  | ⟨60, _⟩ => point 3 3 2
  | ⟨61, _⟩ => point 0 3 2
  | ⟨62, _⟩ => point 0 0 2
  | ⟨63, _⟩ => point 0 0 3
  | ⟨n + 64, h⟩ => by omega

def cycle2 (i : Fin 64) : Vertex4 :=
  match i with
  | ⟨0, _⟩ => point 0 0 0
  | ⟨1, _⟩ => point 1 0 0
  | ⟨2, _⟩ => point 2 0 0
  | ⟨3, _⟩ => point 2 1 0
  | ⟨4, _⟩ => point 2 1 1
  | ⟨5, _⟩ => point 2 2 1
  | ⟨6, _⟩ => point 3 2 1
  | ⟨7, _⟩ => point 3 3 1
  | ⟨8, _⟩ => point 0 3 1
  | ⟨9, _⟩ => point 0 0 1
  | ⟨10, _⟩ => point 0 0 2
  | ⟨11, _⟩ => point 1 0 2
  | ⟨12, _⟩ => point 2 0 2
  | ⟨13, _⟩ => point 2 1 2
  | ⟨14, _⟩ => point 3 1 2
  | ⟨15, _⟩ => point 0 1 2
  | ⟨16, _⟩ => point 1 1 2
  | ⟨17, _⟩ => point 1 2 2
  | ⟨18, _⟩ => point 2 2 2
  | ⟨19, _⟩ => point 3 2 2
  | ⟨20, _⟩ => point 3 3 2
  | ⟨21, _⟩ => point 3 0 2
  | ⟨22, _⟩ => point 3 0 3
  | ⟨23, _⟩ => point 0 0 3
  | ⟨24, _⟩ => point 0 1 3
  | ⟨25, _⟩ => point 1 1 3
  | ⟨26, _⟩ => point 1 1 0
  | ⟨27, _⟩ => point 1 1 1
  | ⟨28, _⟩ => point 1 2 1
  | ⟨29, _⟩ => point 1 3 1
  | ⟨30, _⟩ => point 1 0 1
  | ⟨31, _⟩ => point 2 0 1
  | ⟨32, _⟩ => point 3 0 1
  | ⟨33, _⟩ => point 3 1 1
  | ⟨34, _⟩ => point 0 1 1
  | ⟨35, _⟩ => point 0 2 1
  | ⟨36, _⟩ => point 0 2 2
  | ⟨37, _⟩ => point 0 3 2
  | ⟨38, _⟩ => point 1 3 2
  | ⟨39, _⟩ => point 1 3 3
  | ⟨40, _⟩ => point 1 0 3
  | ⟨41, _⟩ => point 2 0 3
  | ⟨42, _⟩ => point 2 1 3
  | ⟨43, _⟩ => point 3 1 3
  | ⟨44, _⟩ => point 3 2 3
  | ⟨45, _⟩ => point 0 2 3
  | ⟨46, _⟩ => point 1 2 3
  | ⟨47, _⟩ => point 2 2 3
  | ⟨48, _⟩ => point 2 2 0
  | ⟨49, _⟩ => point 3 2 0
  | ⟨50, _⟩ => point 3 3 0
  | ⟨51, _⟩ => point 3 0 0
  | ⟨52, _⟩ => point 3 1 0
  | ⟨53, _⟩ => point 0 1 0
  | ⟨54, _⟩ => point 0 2 0
  | ⟨55, _⟩ => point 1 2 0
  | ⟨56, _⟩ => point 1 3 0
  | ⟨57, _⟩ => point 2 3 0
  | ⟨58, _⟩ => point 2 3 1
  | ⟨59, _⟩ => point 2 3 2
  | ⟨60, _⟩ => point 2 3 3
  | ⟨61, _⟩ => point 3 3 3
  | ⟨62, _⟩ => point 0 3 3
  | ⟨63, _⟩ => point 0 3 0
  | ⟨n + 64, h⟩ => by omega

def cycle0Equiv : Fin 64 ≃ Vertex4 where
  toFun := cycle0
  invFun := rank0Fin
  left_inv := by
    intro i
    native_decide +revert
  right_inv := by
    intro x
    native_decide +revert

def cycle1Equiv : Fin 64 ≃ Vertex4 where
  toFun := cycle1
  invFun := rank1Fin
  left_inv := by
    intro i
    native_decide +revert
  right_inv := by
    intro x
    native_decide +revert

def cycle2Equiv : Fin 64 ≃ Vertex4 where
  toFun := cycle2
  invFun := rank2Fin
  left_inv := by
    intro i
    native_decide +revert
  right_inv := by
    intro x
    native_decide +revert

theorem edgePartition :
    Shared.IsCayleyEdgePartition colorDir := by
  intro x i
  rcases dirWordNat_perm x with h | h | h | h | h | h
  · fin_cases i
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
  · fin_cases i
    · refine ⟨(2 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(1 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢
    · refine ⟨(0 : Shared.TorusColor 3), by simp [colorDir, h, dirOfNat], ?_⟩
      intro c hc
      fin_cases c <;> simp [colorDir, h, dirOfNat] at hc ⊢

theorem cycle0_step :
    ∀ i : Fin 64,
      cycle0 (i + 1) = Shared.cayleyColorStep colorDir 0 (cycle0 i) := by
  native_decide

theorem cycle1_step :
    ∀ i : Fin 64,
      cycle1 (i + 1) = Shared.cayleyColorStep colorDir 1 (cycle1 i) := by
  native_decide

theorem cycle2_step :
    ∀ i : Fin 64,
      cycle2 (i + 1) = Shared.cayleyColorStep colorDir 2 (cycle2 i) := by
  native_decide

theorem colorHamiltonian :
    Shared.IsCayleyColorHamiltonian colorDir := by
  intro c
  fin_cases c
  · exact (Shared.CycleCoordinate.ofFinEquiv
      cycle0Equiv cycle0_step).singleCycle
  · exact (Shared.CycleCoordinate.ofFinEquiv
      cycle1Equiv cycle1_step).singleCycle
  · exact (Shared.CycleCoordinate.ofFinEquiv
      cycle2Equiv cycle2_step).singleCycle

def cayleyDecomposition : Shared.CayleyDecomposition 3 4 where
  colorDir := colorDir
  edgePartition := edgePartition
  colorHamiltonian := colorHamiltonian

theorem ordinary_three_four :
    Shared.CayleyHamiltonDecomposition 3 4 :=
  ⟨cayleyDecomposition⟩

end D3EvenM4
end EvenV11
