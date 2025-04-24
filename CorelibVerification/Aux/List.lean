import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Tactic.Linarith

namespace List

/-- `List.dropWhileN` behaves like `List.dropWhile` but specifies a maximum of elements that are dropped. -/
def dropWhileN (as : List α) (p : α → Bool) (n : ℕ) : List α :=
  (as.take n).dropWhile p ++ as.drop n

@[simp]
theorem dropWhileN_nil : ([] : List α).dropWhileN p n = [] := by
  simp [dropWhileN]

@[simp]
theorem dropWhileN_zero (xs : List α) : xs.dropWhileN p 0 = xs := by
  rfl

@[simp]
theorem dropWhileN_cons_succ (x : α) (xs : List α) (p n) :
    (x::xs).dropWhileN p n.succ = if p x then xs.dropWhileN p n else x::xs := by
  simp only [dropWhileN, dropWhile, drop]
  aesop

theorem dropWhileN_cons_of_pos (x : α) (xs : List α) (p) {n} (h : 0 < n) :
    (x::xs).dropWhileN p n = if p x then xs.dropWhileN p (n - 1) else x::xs := by
  rw [← Nat.succ_pred_eq_of_pos h, dropWhileN_cons_succ]; simp

@[simp]
theorem dropWhile_true (xs : List α) (n) :
    xs.dropWhileN (fun _ => true) n = xs.drop n := by
  induction' xs with x xs ih generalizing n
  · simp
  · induction' n with n
    · simp
    · simp_all

/-- `List.takeWhileN` behaves like `List.takeWhile` but specifies a maximum number of elements that
are taken. -/
def takeWhileN (as : List α) (p : α → Bool) (n : ℕ) : List α := (as.take n).takeWhile p

@[simp]
theorem takeWhileN_nil (p n) : ([] : List α).takeWhileN p n = [] := by
  simp [takeWhileN]

@[simp]
theorem takeWhileN_zero (as : List α) (p) : as.takeWhileN p 0 = [] := by
  simp [takeWhileN]

@[simp]
theorem takeWhileN_cons_succ (a) (as : List α) (p n) :
    (a::as).takeWhileN p (.succ n) = if p a then a::(as.takeWhileN p n) else [] := by
  simp [takeWhileN, takeWhile]
  aesop

theorem takeWhileN_cons_of_pos (a) (as : List α) (p) {n : ℕ} (h : 0 < n) :
    (a::as).takeWhileN p n = if p a then a::(as.takeWhileN p (n - 1)) else [] := by
  rw [← Nat.succ_pred_eq_of_pos h]
  simp [takeWhileN_cons_succ]

theorem takeWhileN_append_dropWhileN (as : List α) :
    as.takeWhileN p n ++ as.dropWhileN p n = as := by
  induction' as generalizing n
  · simp
  · induction' n
    · simp
    · simp only [takeWhileN_cons_succ, dropWhileN_cons_succ]
      aesop

@[simp]
theorem length_takeWhileN (as : List α) :
    (as.takeWhileN p n).length = min n (as.takeWhile p).length := by
  induction' as with _ _ ih generalizing n
  · simp [takeWhile]
  · induction' n
    · simp
    · simp only [takeWhileN_cons_succ, takeWhile, ge_iff_le]
      split_ifs with h
      · simp only [length_cons, h, ge_iff_le, ih, Nat.succ_min_succ]
      · simp [h]

theorem take_pred_tail {as : List α} (h : 0 < n) : as.tail.take (n - 1) = (as.take n).tail := by
  induction' as with a as
  · simp
  · rcases n
    · contradiction
    · simp

@[simp]
theorem head!_eq_head [Inhabited α] {as : List α} (h : ¬ as = []) : as.head! = as.head h := by
  rw [List.head!_eq_head?, List.head?_eq_head]

theorem all_tail {as : List α} (h : as.all p) : as.tail.all p := by
  simp only [all_eq_true] at *
  intro x hx
  apply h _ (mem_of_mem_tail hx)

lemma length_pos_of_ne {as : List α} (h : as ≠ []) : 0 < as.length := by
  rwa [List.length_pos_iff]

-- This one is probably a bit problematic to be a general simp lemma, actually
@[simp]
lemma cons_map_tail_eq (f : α → β) {as : List α} (h : as ≠ []) :
    f (as.head h) :: (as.map f).tail = as.map f := by
  conv_rhs => rw [← List.head_cons_tail as h, List.map_cons, List.map_tail]

lemma ne_empty_of_head?_eq_some {as : List α} (h : as.head? = .some a) :
    as ≠ [] := by
  rcases as <;> simp at *

lemma length_tail_takeWhile [Inhabited α] [DecidableEq α] (as : List α) (h : as ≠ [])
    (h' : p (as.head h)) : as.takeWhile p = as.head h :: (as.tail.takeWhile p) := by
  rcases as with ⟨⟩|⟨a,as⟩
  · simp only [takeWhile_nil, tail_nil, ne_cons_self]
    contradiction
  · simp [takeWhile_cons]
    exact h'
