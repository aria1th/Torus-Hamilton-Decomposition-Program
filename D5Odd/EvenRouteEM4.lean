import D5Odd.EvenRouteE
import Shared.RankCycle

namespace D5Odd

instance : DecidableEq (ARoot5 4) := inferInstance
instance : Fintype (ARoot5 4) := inferInstance
instance : DecidableEq (Vec5 4) := inferInstance
instance : Fintype (Vec5 4) := inferInstance
instance : DecidableEq (Fin 4 → ZMod 4) := inferInstance
instance : Fintype (Fin 4 → ZMod 4) := inferInstance

def LambdaE (S : Mask5) : Color → Direction :=
  if S = mask5 false false false false false then row5 0 1 2 3 4
  else if S = mask5 true false false false false then row5 0 1 3 2 4
  else if S = mask5 false true false false false then row5 0 1 2 4 3
  else if S = mask5 true true false false false then row5 4 1 3 2 0
  else if S = mask5 false false true false false then row5 4 1 2 3 0
  else if S = mask5 true false true false false then row5 4 1 3 0 2
  else if S = mask5 false true true false false then row5 1 0 2 4 3
  else if S = mask5 true true true false false then row5 1 4 3 0 2
  else if S = mask5 false false false true false then row5 1 0 2 3 4
  else if S = mask5 true false false true false then row5 1 3 0 2 4
  else if S = mask5 false true false true false then row5 3 0 2 4 1
  else if S = mask5 true true false true false then row5 4 0 3 2 1
  else if S = mask5 false false true true false then row5 4 2 1 3 0
  else if S = mask5 true false true true false then row5 4 3 1 2 0
  else if S = mask5 false true true true false then row5 3 2 0 4 1
  else if S = mask5 true true true true false then row5 0 1 2 3 4
  else if S = mask5 false false false false true then row5 0 2 1 3 4
  else if S = mask5 true false false false true then row5 0 2 1 4 3
  else if S = mask5 false true false false true then row5 0 2 4 1 3
  else if S = mask5 true true false false true then row5 3 2 4 1 0
  else if S = mask5 false false true false true then row5 2 4 1 3 0
  else if S = mask5 true false true false true then row5 4 2 1 0 3
  else if S = mask5 false true true false true then row5 2 0 1 4 3
  else if S = mask5 true true true false true then row5 0 1 2 3 4
  else if S = mask5 false false false true true then row5 1 0 3 2 4
  else if S = mask5 true false false true true then row5 1 3 0 4 2
  else if S = mask5 false true false true true then row5 1 0 4 2 3
  else if S = mask5 true true false true true then row5 0 1 2 3 4
  else if S = mask5 false false true true true then row5 2 4 3 1 0
  else if S = mask5 true false true true true then row5 0 1 2 3 4
  else if S = mask5 false true true true true then row5 0 1 2 3 4
  else if S = mask5 true true true true true then row5 0 1 2 3 4
  else row5 0 1 2 3 4

def m4RouteEDir (t : Fin 4) (c : Color) (w : Vec5 4) : Direction :=
  if t.val = 0 then c else
  if t.val = 1 then LambdaE (zeroMaskMinusOne w) ((row5 2 0 3 1 4) c) else
  if t.val = 2 then Lambda1 (zeroMaskMinusOne w) ((row5 4 2 0 3 1) c) else
  Lambda1 (zeroMaskMinusOne w) ((row5 0 3 1 4 2) c)

def m4RouteESchedule : LayerSchedule 4 where
  dir := m4RouteEDir

def ColorDirectionBijective (f : Color → Direction) : Prop :=
  (∀ a b : Color, f a = f b → a = b) ∧
    ∀ d : Direction, ∃ c : Color, f c = d

instance (f : Color → Direction) : Decidable (ColorDirectionBijective f) := by
  unfold ColorDirectionBijective
  infer_instance

theorem ColorDirectionBijective.to_bijective {f : Color → Direction}
    (h : ColorDirectionBijective f) :
    Function.Bijective f :=
  ⟨h.1, h.2⟩

set_option maxHeartbeats 3000000 in
-- Checks the finite m=4 exact-cover condition over all root states.
set_option linter.style.nativeDecide false in
theorem m4RouteESchedule_exact : IsLayerExactCover m4RouteESchedule := by
  intro t c y
  have h :
      UniqueDirection fun i : Direction =>
        m4RouteESchedule.dir t c (y.1 - q5 4 i) = i := by
    native_decide +revert
  exact h.existsUnique

set_option maxHeartbeats 3000000 in
-- Checks the finite m=4 Latin condition over all layers and states.
set_option linter.style.nativeDecide false in
theorem m4RouteESchedule_latin : IsScheduleLatin m4RouteESchedule := by
  intro t w
  have h :
      ColorDirectionBijective fun c : Color => m4RouteESchedule.dir t c w := by
    native_decide +revert
  exact h.to_bijective

def m4RouteEReturnQuad (c : Color) (x : Fin 4 → ZMod 4) : Fin 4 → ZMod 4 :=
  quadOfRoot (colorReturn m4RouteESchedule c (rootOfQuad x))

def m4QuadIndex (x : Fin 4 → ZMod 4) : Nat :=
  (x 0).val + 4 * (x 1).val + 16 * (x 2).val + 64 * (x 3).val

def m4RankData0 : Array Nat := #[
  0, 178, 24, 126, 182, 59, 206, 135, 111, 79, 146, 99, 149, 38, 244, 177,
  245, 154, 108, 165, 46, 166, 183, 60, 21, 61, 112, 167, 66, 168, 22, 39,
  193, 201, 235, 224, 109, 225, 47, 202, 147, 203, 110, 62, 113, 7, 67, 169,
  44, 15, 54, 68, 184, 69, 45, 226, 48, 176, 148, 204, 23, 205, 114, 8,
  151, 180, 1, 179, 25, 207, 185, 32, 80, 136, 89, 228, 115, 219, 93, 150,
  128, 127, 246, 94, 186, 95, 155, 208, 90, 26, 81, 137, 209, 40, 116, 220,
  236, 170, 41, 237, 156, 194, 187, 96, 238, 63, 91, 27, 117, 28, 210, 82,
  55, 118, 17, 16, 9, 227, 157, 195, 92, 196, 239, 188, 211, 189, 64, 29,
  2, 105, 152, 104, 158, 33, 70, 181, 240, 49, 74, 197, 100, 198, 212, 190,
  247, 221, 199, 248, 71, 129, 159, 34, 249, 138, 241, 50, 213, 51, 101, 75,
  42, 214, 172, 171, 83, 97, 72, 130, 242, 131, 250, 160, 102, 161, 139, 52,
  133, 30, 56, 119, 73, 120, 84, 18, 251, 19, 98, 132, 140, 243, 103, 162,
  153, 107, 164, 106, 85, 10, 3, 121, 229, 122, 252, 20, 233, 191, 141, 65,
  200, 234, 223, 222, 76, 35, 86, 11, 253, 12, 230, 4, 142, 5, 123, 192,
  14, 53, 43, 215, 87, 216, 77, 173, 231, 174, 36, 13, 124, 254, 143, 6,
  58, 57, 134, 144, 78, 145, 31, 217, 37, 88, 232, 175, 218, 163, 125, 255
]

def m4RankData1 : Array Nat := #[
  0, 210, 190, 154, 133, 209, 117, 122, 9, 180, 106, 19, 66, 61, 191, 18,
  254, 244, 46, 89, 139, 56, 99, 24, 228, 167, 35, 201, 148, 215, 71, 219,
  250, 229, 110, 95, 29, 53, 172, 41, 207, 144, 84, 249, 134, 222, 129, 235,
  8, 208, 116, 121, 65, 179, 105, 157, 255, 60, 120, 17, 132, 183, 126, 78,
  75, 159, 127, 79, 175, 44, 224, 164, 80, 204, 185, 237, 165, 14, 112, 174,
  150, 67, 107, 20, 149, 62, 192, 220, 1, 211, 47, 5, 238, 57, 197, 123,
  26, 216, 72, 58, 135, 245, 130, 90, 21, 230, 100, 25, 162, 168, 36, 202,
  43, 223, 163, 236, 203, 184, 111, 96, 13, 54, 173, 42, 30, 145, 85, 158,
  82, 55, 146, 86, 81, 233, 50, 92, 87, 252, 102, 218, 74, 170, 137, 247,
  226, 15, 113, 138, 124, 76, 160, 155, 93, 176, 118, 225, 10, 181, 205, 186,
  194, 239, 11, 6, 187, 151, 198, 108, 140, 68, 63, 193, 27, 2, 212, 48,
  232, 49, 101, 37, 251, 169, 217, 73, 31, 136, 246, 131, 97, 22, 231, 91,
  242, 98, 23, 142, 166, 34, 200, 4, 214, 70, 196, 241, 243, 39, 189, 153,
  52, 171, 40, 248, 143, 83, 128, 147, 221, 45, 234, 51, 227, 88, 253, 103,
  178, 104, 119, 206, 59, 182, 16, 114, 28, 125, 77, 161, 109, 94, 177, 156,
  33, 69, 3, 213, 32, 195, 240, 12, 38, 188, 152, 7, 115, 141, 199, 64
]

def m4RankData2 : Array Nat := #[
  0, 92, 133, 110, 148, 51, 98, 117, 76, 250, 26, 6, 198, 18, 236, 168,
  68, 225, 11, 56, 47, 1, 93, 81, 125, 173, 13, 40, 127, 243, 206, 153,
  199, 97, 211, 147, 249, 69, 104, 111, 161, 179, 142, 185, 32, 192, 62, 218,
  57, 116, 80, 132, 46, 25, 12, 212, 124, 242, 232, 197, 126, 86, 109, 255,
  135, 87, 163, 34, 65, 129, 227, 194, 186, 36, 106, 213, 219, 113, 233, 71,
  58, 155, 19, 134, 21, 136, 149, 169, 181, 7, 144, 99, 237, 52, 251, 27,
  64, 128, 226, 41, 118, 82, 207, 164, 14, 88, 2, 94, 77, 187, 174, 244,
  35, 200, 143, 63, 105, 193, 156, 20, 48, 22, 70, 180, 154, 162, 33, 112,
  78, 73, 246, 42, 165, 60, 44, 253, 95, 216, 157, 222, 209, 23, 120, 16,
  29, 220, 201, 214, 84, 195, 234, 189, 107, 90, 130, 228, 49, 101, 37, 114,
  176, 59, 145, 252, 150, 53, 74, 247, 66, 166, 137, 8, 72, 182, 238, 170,
  43, 89, 188, 175, 30, 177, 221, 83, 100, 119, 15, 215, 28, 245, 208, 3,
  122, 230, 146, 4, 248, 172, 103, 39, 160, 178, 205, 152, 67, 224, 10, 55,
  240, 79, 158, 121, 45, 24, 141, 184, 31, 191, 61, 217, 139, 96, 210, 254,
  203, 91, 102, 38, 123, 241, 231, 196, 223, 85, 108, 5, 17, 115, 235, 131,
  50, 140, 183, 202, 190, 204, 151, 171, 229, 9, 159, 75, 239, 54, 167, 138
]

def m4RankData3 : Array Nat := #[
  0, 89, 77, 52, 227, 54, 253, 123, 233, 91, 18, 176, 125, 191, 45, 20,
  185, 101, 94, 139, 243, 141, 57, 112, 59, 70, 103, 143, 114, 246, 61, 72,
  162, 2, 212, 34, 214, 229, 169, 96, 36, 238, 216, 231, 98, 11, 116, 171,
  187, 203, 132, 198, 68, 152, 4, 205, 200, 27, 38, 134, 40, 136, 154, 6,
  201, 189, 241, 155, 150, 225, 30, 7, 174, 165, 78, 121, 9, 55, 110, 80,
  87, 192, 46, 21, 208, 128, 83, 157, 25, 210, 32, 23, 41, 167, 85, 159,
  161, 247, 62, 179, 148, 194, 48, 146, 234, 130, 64, 181, 43, 196, 50, 66,
  223, 12, 106, 172, 244, 249, 219, 119, 236, 14, 108, 221, 75, 251, 16, 183,
  184, 81, 252, 122, 53, 90, 17, 254, 69, 190, 92, 124, 245, 126, 19, 177,
  1, 56, 111, 242, 228, 102, 142, 140, 237, 60, 58, 113, 73, 71, 104, 144,
  186, 168, 95, 160, 151, 215, 213, 35, 232, 230, 170, 97, 115, 239, 217, 117,
  163, 3, 51, 67, 206, 204, 133, 199, 37, 153, 5, 39, 99, 28, 137, 135,
  173, 100, 93, 138, 224, 29, 226, 156, 164, 175, 31, 8, 44, 166, 79, 255,
  202, 127, 82, 178, 207, 209, 47, 22, 24, 129, 84, 158, 10, 211, 33, 86,
  88, 193, 105, 145, 147, 248, 63, 180, 26, 195, 49, 65, 42, 131, 197, 182,
  188, 240, 218, 118, 149, 13, 107, 220, 235, 250, 15, 120, 74, 76, 109, 222
]

def m4RankData4 : Array Nat := #[
  0, 82, 242, 111, 1, 20, 123, 76, 77, 231, 165, 138, 208, 153, 67, 197,
  237, 211, 12, 103, 104, 48, 58, 184, 185, 195, 243, 85, 86, 105, 183, 166,
  245, 94, 146, 75, 19, 83, 161, 180, 181, 212, 74, 59, 133, 160, 196, 244,
  51, 122, 187, 236, 230, 164, 49, 147, 152, 186, 84, 162, 163, 182, 213, 50,
  198, 220, 154, 188, 149, 247, 38, 215, 32, 240, 25, 202, 62, 90, 5, 43,
  140, 87, 106, 40, 128, 199, 221, 124, 2, 21, 232, 189, 167, 209, 39, 139,
  168, 134, 23, 29, 238, 88, 200, 41, 60, 3, 222, 125, 126, 22, 233, 190,
  127, 246, 37, 214, 148, 239, 24, 30, 31, 89, 201, 42, 61, 4, 223, 234,
  52, 241, 68, 6, 170, 96, 225, 15, 131, 143, 10, 193, 44, 116, 101, 251,
  63, 210, 98, 112, 7, 53, 248, 252, 78, 33, 69, 216, 217, 97, 26, 203,
  218, 141, 13, 191, 129, 8, 99, 113, 114, 54, 249, 253, 79, 34, 70, 27,
  255, 95, 224, 235, 169, 142, 14, 192, 130, 9, 100, 250, 115, 55, 35, 254,
  219, 91, 117, 155, 47, 57, 137, 179, 194, 66, 73, 110, 81, 159, 174, 207,
  45, 156, 107, 204, 150, 171, 175, 118, 119, 92, 226, 16, 132, 144, 11, 102,
  18, 135, 71, 28, 64, 157, 108, 205, 151, 172, 176, 227, 120, 93, 145, 17,
  229, 56, 36, 178, 46, 136, 72, 109, 65, 158, 173, 206, 80, 121, 177, 228
]

def m4RankData (c : Color) : Array Nat :=
  match c with
  | 0 => m4RankData0
  | 1 => m4RankData1
  | 2 => m4RankData2
  | 3 => m4RankData3
  | 4 => m4RankData4

def m4RankZ (c : Color) (x : Fin 4 → ZMod 4) : ZMod 256 :=
  ((m4RankData c).getD (m4QuadIndex x) 0 : ZMod 256)

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 5000000 in
-- Checks the generated five-color, 256-state m=4 rank-step table.
theorem m4RankZ_step :
    ∀ c : Color, ∀ x : Fin 4 → ZMod 4,
      m4RankZ c (m4RouteEReturnQuad c x) = m4RankZ c x + 1 := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 5000000 in
-- Checks that each generated m=4 rank table is bijective onto ZMod 256.
theorem m4RankZ_bijective :
    ∀ c : Color, Function.Bijective (m4RankZ c) := by
  native_decide

theorem m4RouteEReturnQuad_single_cycle (c : Color) :
    IsSingleCycleMap (m4RouteEReturnQuad c) := by
  exact Shared.single_cycle_of_zmod_rank
    (f := m4RouteEReturnQuad c)
    (rank := m4RankZ c)
    (m4RankZ_bijective c)
    (m4RankZ_step c)

theorem colorReturn_m4RouteESchedule_single_cycle (c : Color) :
    IsSingleCycleMap (colorReturn m4RouteESchedule c) := by
  exact single_cycle_of_bijective_semiconj
    (f := m4RouteEReturnQuad c)
    (g := colorReturn m4RouteESchedule c)
    (phi := rootOfQuad)
    (Equiv.bijective (rootQuadEquiv 4))
    (by intro x; unfold m4RouteEReturnQuad; rw [rootOfQuad_quadOfRoot])
    (m4RouteEReturnQuad_single_cycle c)

theorem m4RouteESchedule_allColorHamiltonian :
    AllColorHamiltonian m4RouteESchedule := by
  intro c
  exact colorReturn_m4RouteESchedule_single_cycle c

theorem D5EvenRouteEM4FiniteTarget_unconditional :
    D5EvenRouteEM4FiniteTarget := by
  exact ⟨m4RouteESchedule, m4RouteESchedule_exact, m4RouteESchedule_latin,
    m4RouteESchedule_allColorHamiltonian⟩

theorem D5EvenRouteEAllEvenHamiltonTarget.of_large_unconditional_m4
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenHamiltonTarget.of_nonopen_unconditional_m4
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_nonopen_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenHamiltonTarget.of_theta_unconditional_m4
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_theta_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_large_unconditional_m4
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_nonopen_unconditional_m4
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_nonopen_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_theta_unconditional_m4
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_theta_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_large_unconditional_m4
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_nonopen_unconditional_m4
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_nonopen_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_theta_unconditional_m4
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_theta_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

end D5Odd
