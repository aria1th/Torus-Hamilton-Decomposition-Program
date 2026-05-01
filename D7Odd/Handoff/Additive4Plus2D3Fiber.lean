import D7Odd.Handoff.Additive4Plus2

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

def d3OddSinkCoord {m : Nat} (layer : ZMod m) (fiber : ARoot3 m) :
    ZMod m :=
  fiber.1 2 + layer

def d3OddDirection {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m) (slot : Direction3) :
    Direction3 :=
  if slot = 0 then
    if layer = 0 ∧ d3OddSinkCoord layer fiber ≠ 0 then 1
    else if layer = 1 then 2
    else 0
  else if slot = 1 then
    if layer = 0 then 2
    else if layer = 1 ∧ d3OddSinkCoord layer fiber = 0 then 0
    else 1
  else
    if layer = 0 ∨ layer = 1 then
      if d3OddSinkCoord layer fiber = 0 then 1 else 0
    else 2

def d3OddStep {m : Nat}
    (layer : ZMod m) (slot : Direction3) (fiber : ARoot3 m) :
    ARoot3 m :=
  fiberAddQ (d3OddDirection layer fiber slot) fiber

instance {m : Nat} : DecidablePred (Root3 m) := by
  intro w
  unfold Root3 sum3
  infer_instance

@[simp] theorem fiberAddQ_two {m : Nat} (w : ARoot3 m) :
    fiberAddQ (2 : Direction3) w = w := rfl

def fiberSubQ {m : Nat} (i : Direction3) (w : ARoot3 m) : ARoot3 m :=
  match i.val with
  | 0 => vec3OfPrefix (w.1 0 - 1) (w.1 1)
  | 1 => vec3OfPrefix (w.1 0) (w.1 1 - 1)
  | _ => w

set_option linter.flexible false in
theorem fiberAddQ_fiberSubQ {m : Nat}
    (i : Direction3) (w : ARoot3 m) :
    fiberAddQ i (fiberSubQ i w) = w := by
  apply Subtype.ext
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [fiberAddQ, fiberSubQ, vec3OfPrefix]
  all_goals
    try rw [root3_sink_eq]
    ring

set_option linter.flexible false in
theorem d3OddSinkCoord_fiberSubQ_zero {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m) :
    d3OddSinkCoord layer (fiberSubQ 0 fiber) =
      d3OddSinkCoord layer fiber + 1 := by
  simp [d3OddSinkCoord, fiberSubQ, vec3OfPrefix]
  rw [root3_sink_eq]
  ring

set_option linter.flexible false in
theorem d3OddSinkCoord_fiberSubQ_one {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m) :
    d3OddSinkCoord layer (fiberSubQ 1 fiber) =
      d3OddSinkCoord layer fiber + 1 := by
  simp [d3OddSinkCoord, fiberSubQ, vec3OfPrefix]
  rw [root3_sink_eq]
  ring

theorem d3OddSinkCoord_fiberSubQ_zero_eq_zero_of_eq_neg_one {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m)
    (h : d3OddSinkCoord layer fiber = -1) :
    d3OddSinkCoord layer (fiberSubQ 0 fiber) = 0 := by
  rw [d3OddSinkCoord_fiberSubQ_zero, h]
  ring

theorem d3OddSinkCoord_fiberSubQ_one_eq_zero_of_eq_neg_one {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m)
    (h : d3OddSinkCoord layer fiber = -1) :
    d3OddSinkCoord layer (fiberSubQ 1 fiber) = 0 := by
  rw [d3OddSinkCoord_fiberSubQ_one, h]
  ring

theorem d3OddSinkCoord_fiberSubQ_zero_ne_zero_of_ne_neg_one {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m)
    (h : d3OddSinkCoord layer fiber ≠ -1) :
    d3OddSinkCoord layer (fiberSubQ 0 fiber) ≠ 0 := by
  intro hz
  apply h
  have hsum : d3OddSinkCoord layer fiber + 1 = 0 := by
    simpa [d3OddSinkCoord_fiberSubQ_zero] using hz
  exact add_eq_zero_iff_eq_neg.mp hsum

theorem d3OddSinkCoord_fiberSubQ_one_ne_zero_of_ne_neg_one {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m)
    (h : d3OddSinkCoord layer fiber ≠ -1) :
    d3OddSinkCoord layer (fiberSubQ 1 fiber) ≠ 0 := by
  intro hz
  apply h
  have hsum : d3OddSinkCoord layer fiber + 1 = 0 := by
    simpa [d3OddSinkCoord_fiberSubQ_one] using hz
  exact add_eq_zero_iff_eq_neg.mp hsum

theorem zmod_zero_ne_one_of_two_le {m : Nat} (hm : 2 ≤ m) :
    (0 : ZMod m) ≠ 1 := by
  intro h
  have hcast : ((1 : Nat) : ZMod m) = 0 := by
    simpa [eq_comm] using h
  have hdiv : m ∣ 1 := (ZMod.natCast_eq_zero_iff 1 m).mp hcast
  have hm1 : m = 1 := Nat.dvd_one.mp hdiv
  omega

set_option linter.flexible false in
set_option linter.style.nativeDecide false in
theorem d3OddDirection_rowLatin_of_zero_ne_one {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m)
    (h01 : (0 : ZMod m) ≠ 1) :
    Function.Bijective fun slot : Direction3 =>
      d3OddDirection layer fiber slot := by
  by_cases h0 : layer = 0
  · subst layer
    by_cases hk : (d3OddSinkCoord (m := m) (0 : ZMod m) fiber = 0)
    · simp [d3OddDirection, h01, hk]
      native_decide
    · simp [d3OddDirection, h01, hk]
      native_decide
  · by_cases h1 : layer = 1
    · subst layer
      by_cases hk : (d3OddSinkCoord (m := m) (1 : ZMod m) fiber = 0)
      · simp [d3OddDirection, h0, hk]
        native_decide
      · simp [d3OddDirection, h0, hk]
        native_decide
    · by_cases hk : d3OddSinkCoord layer fiber = 0
      · simp [d3OddDirection, h0, h1, hk]
        native_decide
      · simp [d3OddDirection, h0, h1, hk]
        native_decide

theorem d3OddDirection_rowLatin_of_two_le {m : Nat}
    (hm : 2 ≤ m) (layer : ZMod m) (fiber : ARoot3 m) :
    Function.Bijective fun slot : Direction3 =>
      d3OddDirection layer fiber slot :=
  d3OddDirection_rowLatin_of_zero_ne_one layer fiber
    (zmod_zero_ne_one_of_two_le hm)

theorem d3OddStep_surjective_of_zero_ne_one {m : Nat}
    (layer : ZMod m) (slot : Direction3)
    (h01 : (0 : ZMod m) ≠ 1) :
    Function.Surjective (d3OddStep (m := m) layer slot) := by
  intro target
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa [eq_comm] using h01
  fin_cases slot
  · by_cases h0 : layer = 0
    · subst layer
      by_cases htarget :
          d3OddSinkCoord (m := m) (0 : ZMod m) target = -1
      · refine ⟨fiberSubQ 0 target, ?_⟩
        have hs :=
          d3OddSinkCoord_fiberSubQ_zero_eq_zero_of_eq_neg_one
            (m := m) (0 : ZMod m) target htarget
        simp [d3OddStep, d3OddDirection, hs, h01, fiberAddQ_fiberSubQ]
      · refine ⟨fiberSubQ 1 target, ?_⟩
        have hs :=
          d3OddSinkCoord_fiberSubQ_one_ne_zero_of_ne_neg_one
            (m := m) (0 : ZMod m) target htarget
        simp [d3OddStep, d3OddDirection, hs, fiberAddQ_fiberSubQ]
    · by_cases h1 : layer = 1
      · subst layer
        refine ⟨target, ?_⟩
        simp [d3OddStep, d3OddDirection, h10]
      · refine ⟨fiberSubQ 0 target, ?_⟩
        simp [d3OddStep, d3OddDirection, h0, h1, fiberAddQ_fiberSubQ]
  · by_cases h0 : layer = 0
    · subst layer
      refine ⟨target, ?_⟩
      simp [d3OddStep, d3OddDirection]
    · by_cases h1 : layer = 1
      · subst layer
        by_cases htarget :
            d3OddSinkCoord (m := m) (1 : ZMod m) target = -1
        · refine ⟨fiberSubQ 0 target, ?_⟩
          have hs :=
            d3OddSinkCoord_fiberSubQ_zero_eq_zero_of_eq_neg_one
              (m := m) (1 : ZMod m) target htarget
          simp [d3OddStep, d3OddDirection, h10, hs,
            fiberAddQ_fiberSubQ]
        · refine ⟨fiberSubQ 1 target, ?_⟩
          have hs :=
            d3OddSinkCoord_fiberSubQ_one_ne_zero_of_ne_neg_one
              (m := m) (1 : ZMod m) target htarget
          simp [d3OddStep, d3OddDirection, h10, hs,
            fiberAddQ_fiberSubQ]
      · refine ⟨fiberSubQ 1 target, ?_⟩
        simp [d3OddStep, d3OddDirection, h0, h1, fiberAddQ_fiberSubQ]
  · by_cases h0 : layer = 0
    · subst layer
      by_cases htarget :
          d3OddSinkCoord (m := m) (0 : ZMod m) target = -1
      · refine ⟨fiberSubQ 1 target, ?_⟩
        have hs :=
          d3OddSinkCoord_fiberSubQ_one_eq_zero_of_eq_neg_one
            (m := m) (0 : ZMod m) target htarget
        simp [d3OddStep, d3OddDirection, hs, fiberAddQ_fiberSubQ]
      · refine ⟨fiberSubQ 0 target, ?_⟩
        have hs :=
          d3OddSinkCoord_fiberSubQ_zero_ne_zero_of_ne_neg_one
            (m := m) (0 : ZMod m) target htarget
        simp [d3OddStep, d3OddDirection, hs, fiberAddQ_fiberSubQ]
    · by_cases h1 : layer = 1
      · subst layer
        by_cases htarget :
            d3OddSinkCoord (m := m) (1 : ZMod m) target = -1
        · refine ⟨fiberSubQ 1 target, ?_⟩
          have hs :=
            d3OddSinkCoord_fiberSubQ_one_eq_zero_of_eq_neg_one
              (m := m) (1 : ZMod m) target htarget
          simp [d3OddStep, d3OddDirection, h10, hs,
            fiberAddQ_fiberSubQ]
        · refine ⟨fiberSubQ 0 target, ?_⟩
          have hs :=
            d3OddSinkCoord_fiberSubQ_zero_ne_zero_of_ne_neg_one
              (m := m) (1 : ZMod m) target htarget
          simp [d3OddStep, d3OddDirection, h10, hs,
            fiberAddQ_fiberSubQ]
      · refine ⟨target, ?_⟩
        simp [d3OddStep, d3OddDirection, h0, h1]

theorem d3OddStep_bijective_of_zero_ne_one {m : Nat} [NeZero m]
    (layer : ZMod m) (slot : Direction3)
    (h01 : (0 : ZMod m) ≠ 1) :
    Function.Bijective (d3OddStep (m := m) layer slot) :=
  (Fintype.bijective_iff_surjective_and_card _).2
    ⟨d3OddStep_surjective_of_zero_ne_one layer slot h01, rfl⟩

theorem d3OddStep_bijective_of_two_le {m : Nat}
    (hm : 2 ≤ m) (layer : ZMod m) (slot : Direction3) :
    Function.Bijective (d3OddStep (m := m) layer slot) :=
  haveI : NeZero m := ⟨by omega⟩
  d3OddStep_bijective_of_zero_ne_one layer slot
    (zmod_zero_ne_one_of_two_le hm)

end Additive4Plus2
end Handoff
end D7Odd
