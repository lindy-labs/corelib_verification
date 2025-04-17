import Mathlib.Data.BitVec
import Aegis.Types

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

theorem usubOverflow_iff (x y : BitVec w) :
    x.usubOverflow y ↔ x.toNat < y.toNat := by
  simp [BitVec.usubOverflow]

@[aesop forward safe]
theorem le_of_not_usubOverflow {x y : BitVec w} (h : x.usubOverflow y = «false») :
    y.toNat ≤ x.toNat := by
  have := (not_iff_not.mpr (BitVec.usubOverflow_iff x y)).mp (ne_true_of_eq_false h)
  omega

@[aesop forward safe]
theorem lt_of_not_usubOverflow {x y : BitVec w} (h : x.usubOverflow y) :
    x.toNat < y.toNat := by
  rw [BitVec.usubOverflow_iff] at h
  omega

end BitVec

namespace Sierra

/- Conversions from uxxx to felt252 -/
def UInt8.toFelt (x : UInt8) : F := x.toFin.castLE (m := PRIME) (by simp [PRIME])

def UInt16.toFelt (x : UInt16) : F := x.toFin.castLE (m := PRIME) (by simp [PRIME])

def UInt32.toFelt (x : UInt32) : F := x.toFin.castLE (m := PRIME) (by simp [PRIME])

def UInt64.toFelt (x : UInt64) : F := x.toFin.castLE (m := PRIME) (by simp [PRIME])

def UInt128.toFelt (x : UInt128) : F := x.toFin.castLE (m := PRIME) (by simp [PRIME])


end Sierra
