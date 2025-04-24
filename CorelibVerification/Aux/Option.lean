import Mathlib.Data.Option.Basic

namespace Option

def toSum (x : Option α) : α ⊕ Unit := x.elim (.inr ()) .inl

@[simp]
theorem toSum_some (x : α) : (some x).toSum = .inl x := rfl

@[simp]
theorem toSum_none : (none : Option α).toSum = .inr () := rfl

@[simp]
theorem filter_decide_true_some {p : α → Prop} [DecidablePred p] {a : α} (h : p a) :
    Option.filter (fun x => decide (p x)) (.some a) = .some a := by
  simp_all [Option.filter]

@[simp]
theorem filter_decide_false_some {p : α → Prop} [DecidablePred p] {a : α} (h : ¬ p a) :
    Option.filter (fun x => decide (p x)) (.some a) = .none := by
  simp_all [Option.filter]

@[simp]
theorem isSome_filter_some (x : α) : Option.isSome (Option.filter p (.some x)) = p x := by
  by_cases p x <;> simp_all [Option.filter]

theorem filter_eq_none_iff {x : Option α} {p : α → Bool} :
    (Option.filter p x) = .none ↔ (x.isNone ∨ ∃ a, x = .some a ∧ ¬ p a) := by
  rcases x with (_|x)
  · simp
  · simp only [Option.filter, ite_eq_right_iff, isNone_some, some.injEq, Bool.not_eq_true,
      exists_eq_left', false_or]
    constructor
    · intro h; by_contra h'; simp_all
    · aesop

theorem filter_eq_some_iff {x : Option α} {p : α → Bool} :
    (Option.filter p x) = .some a ↔ (p a ∧ x = .some a) := by
  rcases x with (_|x)
  · simp
  · simp only [Option.filter, some.injEq]
    aesop

theorem inr_eq_toSum_iff (x : Unit) (y : Option α) : .inr x = y.toSum ↔ y = .none := by
  rcases y <;> simp

theorem inl_eq_toSum_iff (x : α) (y : Option α) : .inl x = y.toSum ↔ y = .some x := by
  rcases y <;> aesop
