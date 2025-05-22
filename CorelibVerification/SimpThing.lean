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
  aesop
