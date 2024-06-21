import CorelibVerification.Aux.ZMod

namespace Sierra

def U256_MOD := 115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- UInt256 is defined as a non-transparent definition to avoid importing all the instances
  for pairs of rings. First component is the "low" part of the integer, the second one the "high"
  part. -/
def UInt256 := UInt128 × UInt128

instance U128_MOD_pos : Fact (U128_MOD > 0) := ⟨by norm_num[U128_MOD]⟩

instance one_le_U128_MOD : Fact (1 ≤ U128_MOD) := ⟨by norm_num[U128_MOD]⟩

instance : NeZero U256_MOD := ⟨by norm_num[U256_MOD]⟩

theorem U256_MOD_eq_mul : U256_MOD = U128_MOD * U128_MOD := by norm_num[U128_MOD, U256_MOD]

@[simp] theorem U256_MOD_div : U256_MOD / U128_MOD = U128_MOD := by norm_num[U128_MOD, U256_MOD]

theorem U128_MOD_dvd_U256_MOD : U128_MOD ∣ U256_MOD := by norm_num[U128_MOD, U256_MOD]

namespace UInt256

variable (p q : UInt256)

def val : ℕ := U128_MOD * p.2.val + p.1.val

theorem val_lt : p.val < U256_MOD := by
  simp only [val]
  apply lt_of_lt_of_le (add_lt_add_left (ZMod.val_lt _) _)
  trans
  · apply add_le_add_right
    apply (mul_le_mul_left U128_MOD_pos.out).mpr
    apply Nat.le_of_lt_succ
    apply ZMod.val_lt
  norm_num [U256_MOD, U128_MOD]

theorem val_lt_U128_MOD_iff : p.val < U128_MOD ↔ p.2 = 0 := by
  simp only [val]
  constructor
  · intro h
    have := Nat.lt_of_add_lt h
    rwa [mul_lt_iff_lt_one_right U128_MOD_pos.out, @Nat.lt_one_iff, ZMod.val_eq_zero] at this
  · intro h; rw [h]
    simp only [ZMod.val_zero, mul_zero, zero_add]
    apply p.1.val_lt

theorem U128_MOD_le_val_iff : U128_MOD ≤ p.val ↔ p.2 ≠ 0 := by
  rw [← not_iff_not, not_le, val_lt_U128_MOD_iff]
  simp

protected def add : UInt256 where
  fst := p.1 + q.1
  snd := p.2 + q.2 + if p.1.val + q.1.val < U128_MOD then 0 else 1

instance (priority := high) : Add UInt256 := ⟨UInt256.add⟩

protected theorem add_def :
    p + q = ⟨p.1 + q.1, p.2 + q.2 + if p.1.val + q.1.val < U128_MOD then 0 else 1⟩ :=
  rfl

theorem val_add_of_lt (h : p.val + q.val < U256_MOD) : (p + q).val = p.val + q.val := by
  rcases p with ⟨pₗ, pₕ⟩; rcases q with ⟨qₗ, qₕ⟩
  simp [val, UInt256.add_def] at h ⊢
  split_ifs with hlt
  · rw [add_zero, ZMod.val_add_of_lt hlt]
    by_cases hlt' : pₕ.val + qₕ.val < U128_MOD
    · rw [ZMod.val_add_of_lt hlt']
      ring_nf
    · exfalso; rw [← not_le] at h; apply h
      ring_nf
      rw [← mul_add]
      rw [not_lt] at hlt'
      apply le_trans _ (add_le_add_right (add_le_add_right (Nat.mul_le_mul_left _ hlt') _) _)
      apply le_trans _ (Nat.le_add_right _ _)
      apply le_trans _ (Nat.le_add_right _ _)
      exact le_of_eq U256_MOD_eq_mul
  · rw [not_lt] at hlt
    ring_nf at h; rw [← mul_add] at h
    have hlt'' : pₕ.val + qₕ.val < U128_MOD := by
      replace h := Nat.lt_of_add_lt (Nat.lt_of_add_lt h)
      rw [U256_MOD_eq_mul] at h
      exact lt_of_mul_lt_mul_left h (Nat.zero_le _)
    have hlt' : pₗ.val + qₗ.val < 2 * U128_MOD := by
      rw [two_mul]
      exact add_lt_add (ZMod.val_lt _) (ZMod.val_lt _)
    have hlt''' : (pₕ + qₕ).val + (1 : UInt128).val < U128_MOD := by
      rw [ZMod.val_add_of_lt hlt'']
      rw [add_assoc] at h
      have := add_lt_of_add_lt_left h hlt
      rwa [← mul_add_one U128_MOD, ← Nat.lt_div_iff_mul_lt U128_MOD_dvd_U256_MOD, U256_MOD_div,
        ← ZMod.val_one U128_MOD] at this
    rw [ZMod.val_add pₗ qₗ, Nat.mod_eq_of_le_of_lt hlt hlt', ZMod.val_add_of_lt hlt''',
      ZMod.val_add_of_lt hlt'', ZMod.val_one, mul_add, mul_add, mul_one, add_assoc,
      add_comm U128_MOD, Nat.sub_add_cancel hlt]
    ac_rfl

-- TODO generalize the following lemma
/-- Characterization of overflow in U256. -/
theorem val_add_val_lt_iff : U256_MOD ≤ p.val + q.val ↔
    (U128_MOD ≤ p.2.val + q.2.val
    ∨ U128_MOD ≤ p.1.val + q.1.val ∧ U128_MOD ≤ p.2.val + q.2.val + 1) := by
  constructor
  · rw [← not_imp_not, not_le, not_or, not_le, not_and_or, not_le, not_le]
    rintro ⟨h,(h'|h')⟩ <;> simp only [val] <;> ring_nf <;> rw [add_assoc, ← mul_add]
    · rw [Nat.lt_iff_le_pred U128_MOD_pos.out] at h h'
      apply lt_of_le_of_lt (Nat.add_le_add_left h' _)
      apply lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _) _
      norm_num [U128_MOD, U256_MOD]
    · replace h' := Nat.lt_sub_of_add_lt h'; rw [Nat.lt_iff_le_pred (by norm_num [U128_MOD])] at h'
      have h := Nat.add_lt_add p.1.val_lt q.1.val_lt
      rw [Nat.lt_iff_le_pred (by norm_num [U128_MOD, U256_MOD])] at h
      apply lt_of_le_of_lt (Nat.add_le_add_left h _)
      apply lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _ h') _) _
      norm_num [U128_MOD, U256_MOD]
  · rintro (h|⟨h,h'⟩) <;> simp only [val] <;> ring_nf <;> rw [add_assoc, ← mul_add]
    · exact Nat.le_add_of_le_left (Nat.mul_le_mul_left U128_MOD h)
    · refine le_trans ?_ (Nat.add_le_add_left h _)
      refine le_trans ?_ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le_of_le_add h')) _)
      norm_num [U128_MOD, U256_MOD]

protected def sub : UInt256 where
  fst := p.1 - q.1
  snd := p.2 - q.2 - if p.1.val < q.1.val then 1 else 0

instance : Sub UInt256 := ⟨UInt256.sub⟩

protected theorem sub_def :
    p - q = ⟨p.1 - q.1, p.2 - q.2 - if p.1.val < q.1.val then 1 else 0⟩ :=
  rfl

theorem val_lt_val_iff : p.val < q.val ↔
    (p.2.val < q.2.val ∨ p.1.val < q.1.val ∧ p.2.val = q.2.val) := by
  constructor
  · rw [← not_imp_not, not_lt, not_or, not_and_or, not_lt, not_lt]
    rintro ⟨h,(h'|h')⟩ <;> simp only [val]
    · apply le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _)
      apply Nat.add_le_add_left h'
    · replace h := Nat.lt_of_le_of_ne h (Ne.symm h')
      rw [← Nat.add_one_le_iff] at h
      apply le_trans _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _)
      rw [mul_add, mul_one, add_assoc]
      apply Nat.add_le_add_left
      apply Nat.le_add_of_le_left
      exact le_of_lt q.1.val_lt
  · rintro (h|⟨h,h'⟩) <;> simp only [val]
    · rw [← Nat.add_one_le_iff] at h ⊢
      apply le_trans _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _)
      rw [mul_add, mul_one, add_assoc, add_assoc]
      apply Nat.add_le_add_left
      apply Nat.le_add_of_le_left
      rw [Nat.add_one_le_iff]
      exact p.1.val_lt
    · rw [h']; apply Nat.add_lt_add_left h

/-- Multiplication on `UInt256` as implemented by `u256_overflow_mul`. -/
protected def mul : UInt256 where
  fst := p.1 * q.1
  snd := ZMod.hmul p.1 q.1 + p.1 * q.2 + p.2 * q.1

instance : Mul UInt256 := ⟨UInt256.mul⟩

protected theorem mul_def : p * q = ⟨p.1 * q.1, ZMod.hmul p.1 q.1 + p.1 * q.2 + p.2 * q.1⟩ :=
  rfl

@[simp]
theorem val_mul_of_low (p q : UInt128) :
  UInt256.val (HMul.hMul (α := UInt256) (β := UInt256) ⟨p, 0⟩ ⟨q, 0⟩) = p.val * q.val := by
  simp [UInt256.mul_def, UInt256.val, ← ZMod.val_mul_val_eq_hmul]

protected def zero : UInt256 where
  fst := 0
  snd := 0

instance : Zero UInt256 := ⟨UInt256.zero⟩

protected theorem zero_def : (0 : UInt256) = (0, 0) := rfl
