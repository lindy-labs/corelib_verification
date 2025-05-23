import Mathlib

example (a b : BitVec 128 × BitVec 128) (ρ : BitVec 128 × BitVec 128 ⊕ Unit) : (∃ ref5 ref6 ref7 ref8,
    (ref5, ref6) =
        (a + b,
          match decide ¬(a.2 ++ a.1).uaddOverflow (b.2 ++ b.1) = «true» with
          | «false» => Sum.inl ()
          | «true» => Sum.inr ()) ∧
      (Sum.inl ref7 = ref6 ∧ Sum.inl ref5 = ρ ∨ Sum.inr ref8 = ref6 ∧ Sum.inr () = ρ)) →
  ¬(a.2 ++ a.1).uaddOverflow (b.2 ++ b.1) = «true» ∧ ρ = Sum.inl (a + b) ∨
    (a.2 ++ a.1).uaddOverflow (b.2 ++ b.1) = «true» ∧ ρ = Sum.inr ()
 := by
  sorry --aesop


abbrev Sierra.UInt32 := BitVec 32

abbrev Sierra.UInt128 := BitVec 128

abbrev Sierra.Bytes31 := BitVec 248

abbrev Sierra.F := ZMod 3618502788666131213697322783095070105623107215331596699973092056135872020481

abbrev Sierra.ByteArray := List Bytes31 × Sierra.F × Sierra.UInt32

example (v : Sierra.UInt128) (b : Sierra.UInt32) (h : b < 16) :
    BitVec.umod v (1#128 <<< (8#32 * b)) = BitVec.zeroExtend 128 (BitVec.extractLsb' (BitVec.toNat b) 128 v) := by
  unfold Sierra.UInt32 Sierra.UInt128 at *
  --bv_decide
  sorry

example
    (ρ : Sierra.ByteArray × Unit ⊕ Unit × List Sierra.F)
    (w7 w8 : Sierra.UInt32) (w10 : BitVec 248) (w9 : Sierra.F)
    (w5 : Sierra.F ⊕ Unit × List Sierra.F)
    (h₁ : ¬(31#32).usubOverflow w8 = «true» ∧ (Sum.inl w7 : Sierra.UInt32 ⊕ Unit × List Sierra.F) = Sum.inl (31#32 - w8) ∨
      (31#32).usubOverflow w8 = «true» ∧ (Sum.inl w7 : Sierra.UInt32 ⊕ Unit × List Sierra.F).isRight = «true»)
    (h₂ : w7 ≤ 31 ∧ w5 = Sum.inl ((1 <<< (8 * BitVec.toNat w7)) : Sierra.F) ∨ 31 < w7 ∧ w5.isRight = «true»)
    (h₃ : Sum.inr w3 = w5 ∧ Sum.inr w3 = ρ) :
    31#32 < w8 ∧ ρ.isRight = «true» := by
  aesop
  sorry



#eval Lean.versionString
