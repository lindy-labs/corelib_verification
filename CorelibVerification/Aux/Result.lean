import Mathlib.Data.Sum.Basic
import CorelibVerification.Load

namespace Sierra

def Result (α : Type) : Type := α ⊕ List F

namespace Result

variable {α : Type} [Inhabited α] (x : Result α)

def fails := Sum.isRight x

@[simp]
lemma fails_inr (err : List F) : fails (α := α) (.inr err) = .true :=
  rfl

@[simp]
lemma fails_inl (a : α) : fails (.inl a) = .false :=
  rfl

def succeeds := Sum.isLeft x

@[simp]
lemma succeeds_inr (err : List F) : succeeds (α := α) (.inr err) = .false :=
  rfl

@[simp]
lemma succeeds_inl (a : α) : succeeds (.inl a) = .true :=
  rfl

def get! := x.getLeft?.get!

@[simp]
lemma get!_inl (a : α) : get! (.inl a) = a :=
  rfl

@[simp]
lemma get!_inr (err : List F) : get! (α := α) (.inr err) = default :=
  rfl
