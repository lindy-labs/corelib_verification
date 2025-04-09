import Mathlib.Data.BitVec

namespace BitVec

theorem uaddOverflow_iff (x y : BitVec w) :
    x.uaddOverflow y ↔ x.toNat + y.toNat ≥ 2 ^ w := by
  simp [BitVec.uaddOverflow]

@[aesop forward safe]
theorem lt_of_not_uaddOverflow {x y : BitVec w} (h : x.uaddOverflow y = «false») :
    x.toNat + y.toNat < 2 ^ w := by
  have := (not_iff_not.mpr (BitVec.uaddOverflow_iff x y)).mp (ne_true_of_eq_false h)
  omega

@[aesop forward safe]
theorem le_of_uaddOverflow {x y : BitVec w} (h : x.uaddOverflow y) :
    2 ^ w ≤ x.toNat + y.toNat := by
  rw [BitVec.uaddOverflow_iff] at h
  omega
