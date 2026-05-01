import D7Odd.GateSpace

namespace D7Odd

namespace Gate

variable {m : Nat} [NeZero m]

def phi : Gate m -> Gate m
  | C0 a s hs => C0 (a - 1) s hs
  | C5 a s hs => C5 (a - 1) s hs
  | S0 a b => S0 (a - 1) b
  | S3 a b => S3 (a - 1) (b + 1)

def nmod : Gate m -> Gate m
  | C0 a s hs => C5 a s hs
  | C5 a s _ => S0 a s
  | S0 a b => S3 a b
  | S3 a b =>
      if hb : b = 0 then
        S0 a 0
      else
        C0 a b hb

def Ftag : Gate m -> Gate m :=
  nmod ∘ phi

@[simp] theorem Ftag_C0 (a s : ZMod m) (hs : s ≠ 0) :
    Ftag (C0 a s hs) = C5 (a - 1) s hs := rfl

@[simp] theorem Ftag_C5 (a s : ZMod m) (hs : s ≠ 0) :
    Ftag (C5 a s hs) = S0 (a - 1) s := rfl

@[simp] theorem Ftag_S0 (a b : ZMod m) :
    Ftag (S0 a b) = S3 (a - 1) b := rfl

theorem Ftag_S3_eq (a b : ZMod m) (hb : b = -1) :
    Ftag (S3 a b) = S0 (a - 1) 0 := by
  subst b
  simp [Ftag, phi, nmod]

theorem Ftag_S3_ne (a b : ZMod m) (hb : b ≠ -1) :
    Ftag (S3 a b) =
      C0 (a - 1) (b + 1) (mt eq_neg_of_add_eq_zero_left hb) := by
  simp [Ftag, phi, nmod, mt eq_neg_of_add_eq_zero_left hb]

def Reaches (g h : Gate m) : Prop :=
  exists n : Nat, Ftag^[n] g = h

theorem reaches_refl (g : Gate m) : Reaches g g := by
  exact ⟨0, by simp⟩

theorem reaches_trans {g h k : Gate m} (hgh : Reaches g h) (hhk : Reaches h k) :
    Reaches g k := by
  rcases hgh with ⟨n, hn⟩
  rcases hhk with ⟨r, hr⟩
  refine ⟨r + n, ?_⟩
  rw [Function.iterate_add_apply, hn, hr]

theorem reaches_step (g : Gate m) : Reaches g (Ftag g) := by
  exact ⟨1, by simp⟩

theorem reaches_S0_S3 (a b : ZMod m) :
    Reaches (S0 a b) (S3 (a - 1) b) := by
  exact reaches_step _

theorem reaches_S0_C0_of_ne (a b : ZMod m) (hb : b ≠ -1) :
    Reaches (S0 a b) (C0 ((a - 1) - 1) (b + 1)
      (mt eq_neg_of_add_eq_zero_left hb)) := by
  refine ⟨2, ?_⟩
  simp [Function.iterate_succ_apply', Ftag_S3_ne, hb]

theorem reaches_S0_C5_of_ne (a b : ZMod m) (hb : b ≠ -1) :
    Reaches (S0 a b) (C5 (((a - 1) - 1) - 1) (b + 1)
      (mt eq_neg_of_add_eq_zero_left hb)) := by
  refine ⟨3, ?_⟩
  simp [Function.iterate_succ_apply', Ftag_S3_ne, hb]

theorem reaches_S0_next_of_ne (a b : ZMod m) (hb : b ≠ -1) :
    Reaches (S0 a b) (S0 ((((a - 1) - 1) - 1) - 1) (b + 1)) := by
  refine ⟨4, ?_⟩
  simp [Function.iterate_succ_apply', Ftag_S3_ne, hb]

theorem reaches_S0_next_of_eq (a b : ZMod m) (hb : b = -1) :
    Reaches (S0 a b) (S0 ((a - 1) - 1) 0) := by
  refine ⟨2, ?_⟩
  subst b
  simp [Function.iterate_succ_apply', Ftag_S3_eq]

theorem reaches_S0_ladder_step (A b : ZMod m) (hb : b ≠ -1) :
    Reaches (S0 (A - 4 * b) b) (S0 (A - 4 * (b + 1)) (b + 1)) := by
  convert reaches_S0_next_of_ne (a := A - 4 * b) b hb using 2
  ring

theorem reaches_S0_ladder_wrap (A : ZMod m) :
    Reaches (S0 (A - 4 * (-1 : ZMod m)) (-1 : ZMod m)) (S0 (A + 2) 0) := by
  convert reaches_S0_next_of_eq (a := A - 4 * (-1 : ZMod m)) (-1 : ZMod m) rfl using 2
  ring

theorem natCast_pred_eq_neg_one (m : Nat) [NeZero m] :
    (((m - 1 : Nat) : ZMod m) = -1) := by
  rw [eq_neg_iff_add_eq_zero]
  have hsum : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt (NeZero.pos m))
  have hsum_cast : (((m - 1 + 1 : Nat) : ZMod m) = 0) := by
    rw [hsum, ZMod.natCast_self]
  simpa [Nat.cast_add] using hsum_cast

theorem natCast_ne_neg_one_of_succ_lt {k : Nat} (hk : k + 1 < m) :
    ((k : ZMod m) ≠ -1) := by
  intro h
  have hmpos : 0 < m := NeZero.pos m
  have hpred : (((m - 1 : Nat) : ZMod m) = -1) := natCast_pred_eq_neg_one m
  have hklt : k < m := by omega
  have hpredlt : m - 1 < m := Nat.sub_lt hmpos zero_lt_one
  have hkpred : k ≠ m - 1 := by omega
  exact (zmod_natCast_ne_of_lt' hklt hpredlt hkpred) (h.trans hpred.symm)

theorem reaches_S0_ladder_nat (A : ZMod m) :
    forall k : Nat, k < m ->
      Reaches (S0 A 0) (S0 (A - 4 * (k : ZMod m)) (k : ZMod m))
  | 0, _ => by
      convert reaches_refl (S0 A 0) using 2
      · ring
      · norm_num
  | k + 1, hk => by
      have hk' : k < m := by omega
      have hprev := reaches_S0_ladder_nat A k hk'
      have hstep := reaches_S0_ladder_step (A := A) (b := (k : ZMod m))
        (natCast_ne_neg_one_of_succ_lt (m := m) hk)
      convert reaches_trans hprev hstep using 2
      · push_cast
        ring_nf
      · norm_num [Nat.cast_add]

theorem reaches_S0_full_block (A : ZMod m) :
    Reaches (S0 A 0) (S0 (A + 2) 0) := by
  have hmpos : 0 < m := NeZero.pos m
  have hlast := reaches_S0_ladder_nat A (m - 1) (Nat.sub_lt hmpos zero_lt_one)
  have hlast' : Reaches (S0 A 0) (S0 (A - 4 * (-1 : ZMod m)) (-1 : ZMod m)) := by
    convert hlast using 2
    · rw [natCast_pred_eq_neg_one]
    · rw [natCast_pred_eq_neg_one]
  exact reaches_trans hlast' (reaches_S0_ladder_wrap A)

theorem reaches_S0_add_two_mul_nat (A : ZMod m) :
    forall n : Nat, Reaches (S0 A 0) (S0 (A + 2 * (n : ZMod m)) 0)
  | 0 => by
      convert reaches_refl (S0 A 0) using 2
      ring
  | n + 1 => by
      have hprev := reaches_S0_add_two_mul_nat A n
      have hstep := reaches_S0_full_block (A := A + 2 * (n : ZMod m))
      convert reaches_trans hprev hstep using 2
      push_cast
      ring

omit [NeZero m] in
theorem isUnit_two_of_odd (hodd : Odd m) : IsUnit (2 : ZMod m) := by
  change IsUnit ((2 : Nat) : ZMod m)
  rw [ZMod.isUnit_iff_coprime]
  exact hodd.coprime_two_left

theorem exists_two_mul_natCast_eq_of_odd (hodd : Odd m) (A : ZMod m) :
    exists n : Nat, 2 * (n : ZMod m) = A := by
  rcases isUnit_two_of_odd (m := m) hodd with ⟨u, hu⟩
  let B : ZMod m := ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * A
  have huinv : (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
    simp
  have hB : 2 * B = A := by
    rw [← hu]
    calc
      (u : ZMod m) * (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * A)
          = ((u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m)) * A := by ring
      _ = 1 * A := by rw [huinv]
      _ = A := by simp
  rcases ZMod.natCast_zmod_surjective B with ⟨n, hn⟩
  exact ⟨n, by simpa [B, hn] using hB⟩

theorem reaches_S0_zero_to_S0_zero_of_odd (hodd : Odd m) (A : ZMod m) :
    Reaches (S0 0 0 : Gate m) (S0 A 0) := by
  rcases exists_two_mul_natCast_eq_of_odd (m := m) hodd A with ⟨n, hn⟩
  convert reaches_S0_add_two_mul_nat (A := (0 : ZMod m)) n using 2
  rw [zero_add, hn]

theorem reaches_S0_of_odd (hodd : Odd m) (a b : ZMod m) :
    Reaches (S0 0 0 : Gate m) (S0 a b) := by
  have hstart := reaches_S0_zero_to_S0_zero_of_odd (m := m) hodd (a + 4 * b)
  have hladder := reaches_S0_ladder_nat (A := a + 4 * b) b.val (ZMod.val_lt b)
  convert reaches_trans hstart hladder using 2
  · rw [ZMod.natCast_zmod_val]
    ring
  · rw [ZMod.natCast_zmod_val]

theorem reaches_S3_of_odd (hodd : Odd m) (a b : ZMod m) :
    Reaches (S0 0 0 : Gate m) (S3 a b) := by
  have hstart := reaches_S0_of_odd (m := m) hodd (a + 1) b
  have hstep := reaches_S0_S3 (a + 1) b
  convert reaches_trans hstart hstep using 2
  ring

omit [NeZero m] in
theorem sub_one_ne_neg_one_of_ne_zero {s : ZMod m} (hs : s ≠ 0) :
    s - 1 ≠ -1 := by
  intro h
  apply hs
  calc
    s = (s - 1) + 1 := by ring
    _ = (-1 : ZMod m) + 1 := by rw [h]
    _ = 0 := by ring

theorem reaches_C0_of_odd (hodd : Odd m) (a s : ZMod m) (hs : s ≠ 0) :
    Reaches (S0 0 0 : Gate m) (C0 a s hs) := by
  let b : ZMod m := s - 1
  have hb : b ≠ -1 := sub_one_ne_neg_one_of_ne_zero (m := m) hs
  have hstart := reaches_S0_of_odd (m := m) hodd (a + 2) b
  have hstep := reaches_S0_C0_of_ne (a := a + 2) b hb
  convert reaches_trans hstart hstep using 2
  · ring
  · simp [b]

theorem reaches_C5_of_odd (hodd : Odd m) (a s : ZMod m) (hs : s ≠ 0) :
    Reaches (S0 0 0 : Gate m) (C5 a s hs) := by
  let b : ZMod m := s - 1
  have hb : b ≠ -1 := sub_one_ne_neg_one_of_ne_zero (m := m) hs
  have hstart := reaches_S0_of_odd (m := m) hodd (a + 3) b
  have hstep := reaches_S0_C5_of_ne (a := a + 3) b hb
  convert reaches_trans hstart hstep using 2
  · ring
  · simp [b]

theorem every_gate_reaches_of_odd (hodd : Odd m) :
    forall g : Gate m, Reaches (S0 0 0 : Gate m) g
  | C0 a s hs => reaches_C0_of_odd (m := m) hodd a s hs
  | C5 a s hs => reaches_C5_of_odd (m := m) hodd a s hs
  | S0 a b => reaches_S0_of_odd (m := m) hodd a b
  | S3 a b => reaches_S3_of_odd (m := m) hodd a b

theorem every_gate_in_orbit_of_S0_zero (hodd : Odd m) (g : Gate m) :
    exists n : Nat, Ftag^[n] (S0 0 0 : Gate m) = g :=
  every_gate_reaches_of_odd (m := m) hodd g

end Gate

end D7Odd
