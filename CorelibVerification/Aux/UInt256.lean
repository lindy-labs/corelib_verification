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

def toNat : ℕ := (p.2 ++ p.1).toNat

theorem toNat_lt : p.toNat < U256_MOD :=
  (p.2 ++ p.1).isLt

theorem _root_.BitVec.toNat_append' (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = 2 ^ n * x.toNat + y.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_add_lt_is_or y.isLt]
  ac_rfl

theorem pair_toNat {x y : UInt128} : UInt256.toNat (x, y) = x.toNat + y.toNat * U128_MOD := by
  simp [toNat]
  rw [BitVec.toNat_append', U128_MOD]
  ac_rfl

def ofBitVec (x : BitVec 256) : UInt256 :=
  (x.extractLsb' 0 128, x.extractLsb' 128 128)

@[simp]
theorem append_ofBitVec : (ofBitVec x).2 ++ (ofBitVec x).1 = x := by
  ext
  rw [BitVec.getElem_append]
  split_ifs with h
  · simp only [ofBitVec, BitVec.getElem_extractLsb', zero_add, Nat.reduceAdd]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp only [ofBitVec, BitVec.getElem_extractLsb', Nat.reduceAdd]
    have := Nat.add_sub_cancel' (Nat.ge_of_not_lt h)
    congr

@[simp]
theorem fst_ofBitVec_append {x y : UInt128} : (ofBitVec (y ++ x)).1 = x := by
  simp [ofBitVec]
  bv_decide

@[simp]
theorem snd_ofBitVec_append {x y : UInt128} : (ofBitVec (y ++ x)).2 = y := by
  simp [ofBitVec]
  bv_decide

@[ext]
theorem ext (h : p.2 ++ p.1 = q.2 ++ q.1) : p = q := by
  rcases p with ⟨p₁,p₂⟩
  rcases q with ⟨q₁,q₂⟩
  simp only [Nat.reduceAdd] at h
  congr
  · bv_decide
  · bv_decide


/-
theorem toNat_lt_U128_MOD_iff : p.toNat < U128_MOD ↔ p.2 = 0 := by
  simp only [toNat]
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
-/



protected def add : UInt256 := ofBitVec ((p.2 ++ p.1) + (q.2 ++ q.1))

instance (priority := high) : Add UInt256 := ⟨UInt256.add⟩

protected theorem add_def :
    p + q = ofBitVec ((p.2 ++ p.1) + (q.2 ++ q.1)) :=
  rfl

@[simp]
private lemma add_no_overflow (p q : UInt256) (h₁ : ¬ BitVec.uaddOverflow p.1 q.1) :
    p + q = (p.1 + q.1, p.2 + q.2) := by
  simp only [UInt256.add_def, UInt256.ofBitVec, Nat.reduceAdd]
  apply Prod.ext <;> bv_decide

@[simp]
private lemma add_overflow (p q : UInt256) (h₁ : BitVec.uaddOverflow p.1 q.1) :
    p + q = (p.1 + q.1, p.2 + q.2 + 1#128) := by
  simp only [UInt256.add_def, UInt256.ofBitVec, Nat.reduceAdd]
  apply Prod.ext <;> bv_decide

protected def sub : UInt256 := ofBitVec ((p.2 ++ p.1) - (q.2 ++ q.1))
instance : Sub UInt256 := ⟨UInt256.sub⟩

protected theorem sub_def :
    p - q = ofBitVec ((p.2 ++ p.1) - (q.2 ++ q.1)) :=
  rfl

/-
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
-/

/-- Multiplication on `UInt256` as implemented by `u256_overflow_mul`. -/
protected def mul : UInt256  := ofBitVec ((p.2 ++ p.1) * (q.2 ++ q.1))

instance : Mul UInt256 := ⟨UInt256.mul⟩

protected theorem mul_def : p * q = ofBitVec ((p.2 ++ p.1) * (q.2 ++ q.1)) :=
  rfl

/-
@[simp]
theorem val_mul_of_low (p q : UInt128) :
  UInt256.val (HMul.hMul (α := UInt256) (β := UInt256) ⟨p, 0⟩ ⟨q, 0⟩) = p.val * q.val := by
  simp [UInt256.mul_def, UInt256.val, ← ZMod.val_mul_val_eq_hmul]
-/

protected def zero : UInt256 := ofBitVec 0

instance : Zero UInt256 := ⟨UInt256.zero⟩

protected theorem zero_def : (0 : UInt256) = ofBitVec 0 := rfl
