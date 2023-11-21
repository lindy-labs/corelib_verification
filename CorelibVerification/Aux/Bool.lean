import Aegis.Libfuncs.Bool
import Aegis.Aux.Bool

@[simp]
theorem Bool.toSierraBool_not (b : Bool) :
    (Bool.toSierraBool !b) = Sum.swap (Bool.toSierraBool b) := by
  cases b <;> simp only [toSierraBool]

theorem prop_if_true_false {p : Prop} [Decidable p] : (if p then True else False) = p := by aesop

theorem prop_if_false_true {p : Prop} [Decidable p] : (if p then False else True) = ¬ p := by aesop
