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

example (v : Sierra.UInt128) (b : Sierra.UInt32) (h : b < 16) :
    BitVec.umod v (1#128 <<< (8#32 * b)) = BitVec.zeroExtend 128 (BitVec.extractLsb' (BitVec.toNat b) 128 v) := by
  unfold Sierra.UInt32 Sierra.UInt128 at *
  bv_decide
  sorry

#eval Lean.versionString
