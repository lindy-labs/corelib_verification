import Aegis.Libfuncs.Bool
import Aegis.Aux.Bool

@[simp]
theorem Bool.toSierraBool_not (b : Bool) :
    (Bool.toSierraBool !b) = Sum.swap (Bool.toSierraBool b) := by
  cases b <;> simp only [toSierraBool]
