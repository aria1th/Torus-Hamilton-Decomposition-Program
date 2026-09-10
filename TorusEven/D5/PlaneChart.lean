-- STATUS: main-path (the plane chart φ and the terminal supports U_i inside the root space)
import TorusEven.D5.Endpoint
import TorusEven.D5.LayerEval

/-!
# The plane chart

`φ(a, b) = (b, -a-b, 0, a)` parametrizes the terminal plane `Θ`.  The plane permutation
`Jplane (dirs i)` of `LayerEval` corresponds to `j_i` under `φ` (`eq:d5-head`), and the
support `U_i = φ(B_i)`.
-/

namespace TorusEven
namespace D5

variable {m : ℕ} [NeZero m]

def phi (q : Pt m) : Root m := ![q.2, -q.1 - q.2, 0, q.1]

@[simp] theorem phi_apply_0 (q : Pt m) : phi q 0 = q.2 := rfl
@[simp] theorem phi_apply_1 (q : Pt m) : phi q 1 = -q.1 - q.2 := rfl
@[simp] theorem phi_apply_2 (q : Pt m) : phi q 2 = 0 := rfl
@[simp] theorem phi_apply_3 (q : Pt m) : phi q 3 = q.1 := rfl

theorem plane_phi (q : Pt m) : plane (phi q) := by
  refine ⟨rfl, ?_⟩
  simp only [phi_apply_0, phi_apply_1, phi_apply_3]
  ring

theorem planePoint_phi (q : Pt m) : planePoint (phi q) = q := by
  rcases q with ⟨a, b⟩
  rfl

theorem phi_planePoint {x : Root m} (hx : plane x) : phi (planePoint x) = x := by
  obtain ⟨h2, h013⟩ := hx
  funext i
  fin_cases i
  · rfl
  · show -(x 3) - x 0 = x 1
    linear_combination -h013
  · exact h2.symm
  · rfl

theorem phi_injective : Function.Injective (phi : Pt m → Root m) := by
  intro q q' h
  have := congrArg planePoint h
  rwa [planePoint_phi, planePoint_phi] at this

theorem phi_add (q r : Pt m) : phi (q + r) = phi q + phi r := by
  funext i
  fin_cases i <;> simp [phi] <;> ring

theorem phi_sub (q r : Pt m) : phi (q - r) = phi q - phi r := by
  funext i
  fin_cases i <;> simp [phi] <;> ring

theorem phi_avec (k : Fin 3) : phi (avec k : Pt m) = uvec (dirs k) - uvec 1 := by
  fin_cases k <;> (funext i; fin_cases i <;> simp [phi, avec, uvec, dirs])

theorem tauFun_dirs (ω : Equiv.Perm (Fin 3)) (i : Fin 3) : tauFun ω (dirs i) = dirs (ω i) := by
  fin_cases i <;> simp [tauFun, dirs]

/-- `eq:d5-head`: the plane permutation is `j_i` in the chart. -/
theorem Jplane_phi (i : Fin 3) (q : Pt m) : Jplane (dirs i) (phi q) = phi (jmap i q) := by
  unfold Jplane
  rw [if_pos (plane_phi q), planePoint_phi]
  show phi q + uvec (tauFun (omega q) (dirs i)) - uvec (dirs i) = phi (jmap i q)
  rw [tauFun_dirs, jmap, phi_add, phi_sub, phi_avec, phi_avec]
  abel

/-- The support `U_i = φ(B_i)`. -/
def Uset (i : Fin 3) : Set (Root m) := {x | plane x ∧ inB i (planePoint x)}

instance (i : Fin 3) : DecidablePred (· ∈ Uset (m := m) i) := fun x => by
  unfold Uset inB
  exact inferInstance

theorem phi_mem_Uset {i : Fin 3} {q : Pt m} : phi q ∈ Uset i ↔ inB i q := by
  simp [Uset, plane_phi, planePoint_phi]

theorem mem_Uset_iff {i : Fin 3} {x : Root m} : x ∈ Uset i ↔ ∃ q, inB i q ∧ phi q = x := by
  constructor
  · rintro ⟨hp, hb⟩
    exact ⟨planePoint x, hb, phi_planePoint hp⟩
  · rintro ⟨q, hq, rfl⟩
    exact phi_mem_Uset.2 hq

theorem Jplane_of_not_mem (i : Fin 3) {x : Root m} (hx : x ∉ Uset i) : Jplane (dirs i) x = x := by
  unfold Jplane
  split_ifs with hp
  · have hb : ¬ inB i (planePoint x) := fun h => hx ⟨hp, h⟩
    unfold inB at hb
    push_neg at hb
    rw [show tau (omega (planePoint x)) (dirs i) = tauFun (omega (planePoint x)) (dirs i) from rfl,
      tauFun_dirs, hb]
    abel
  · rfl

theorem Jplane_mem (i : Fin 3) (hj : ∀ q : Pt m, inB i q → inB i (jmap i q)) {x : Root m}
    (hx : x ∈ Uset i) : Jplane (dirs i) x ∈ Uset i := by
  obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hx
  rw [Jplane_phi]
  exact phi_mem_Uset.2 (hj q hq)

theorem Jplane_bijective (i : Fin 3) (hj : ∀ q : Pt m, inB i q → inB i (jmap i q))
    (hinj : ∀ q q' : Pt m, inB i q → inB i q' → jmap i q = jmap i q' → q = q') :
    Function.Bijective (Jplane (m := m) (dirs i)) := by
  rw [Finite.injective_iff_bijective.symm]
  intro x y h
  by_cases hx : x ∈ Uset i <;> by_cases hy : y ∈ Uset i
  · obtain ⟨q, hq, rfl⟩ := mem_Uset_iff.1 hx
    obtain ⟨q', hq', rfl⟩ := mem_Uset_iff.1 hy
    rw [Jplane_phi, Jplane_phi] at h
    rw [hinj q q' hq hq' (phi_injective h)]
  · exfalso
    rw [Jplane_of_not_mem i hy] at h
    exact hy (h ▸ Jplane_mem i hj hx)
  · exfalso
    rw [Jplane_of_not_mem i hx] at h
    exact hx (h.symm ▸ Jplane_mem i hj hy)
  · rwa [Jplane_of_not_mem i hx, Jplane_of_not_mem i hy] at h

end D5
end TorusEven
