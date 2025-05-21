import Aegis.Libfuncs.Bool
import Aegis.Aux.Bool

--@[simp]
theorem Bool.toSierraBool_not (b : Bool) :
    (Bool.toSierraBool !b) = Sum.swap (Bool.toSierraBool b) := by
  cases b <;> rfl

@[simp]
theorem Bool.toSierraBool_iff_eq_false (b : Bool) :
    b.toSierraBool = .inl u ↔ (b = .false) := by
  simp [Bool.toSierraBool]
  aesop

@[simp]
theorem Bool.toSierraBool_iff_eq_false' (b : Bool) :
    .inl u = b.toSierraBool ↔ (b = .false) := by
  simp [Bool.toSierraBool]
  aesop

@[simp]
theorem Bool.toSierraBool_iff_eq_true (b : Bool) :
    b.toSierraBool = .inr u ↔ (b = .true) := by
  simp [Bool.toSierraBool]
  aesop

@[simp]
theorem Bool.toSierraBool_iff_eq_true' (b : Bool) :
    .inr u = b.toSierraBool ↔ (b = .true) := by
  simp [Bool.toSierraBool]
  aesop

theorem prop_if_true_false {p : Prop} [Decidable p] : (if p then True else False) = p := by aesop

theorem prop_if_false_true {p : Prop} [Decidable p] : (if p then False else True) = ¬ p := by aesop
