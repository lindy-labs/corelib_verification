import Mathlib.Data.Sum.Basic
import CorelibVerification.Load

namespace Sierra

def PanicResult (α : Type) : Type := α ⊕ Unit × List F

namespace PanicResult

variable {α : Type} [Inhabited α] (x : PanicResult α)

def fails := Sum.isRight x

@[simp]
lemma fails_inr (e) : fails (α := α) (.inr e) = .true :=
  rfl

@[simp]
lemma fails_inl (a : α) : fails (.inl a) = .false :=
  rfl

def succeeds := Sum.isLeft x

@[simp]
lemma succeeds_inr (e) : succeeds (α := α) (.inr e) = .false :=
  rfl

@[simp]
lemma succeeds_inl (a : α) : succeeds (.inl a) = .true :=
  rfl

def get! := x.getLeft?.get!

@[simp]
lemma get!_inl (a : α) : get! (.inl a) = a :=
  rfl

@[simp]
lemma get!_inr (e) : get! (α := α) (.inr e) = default :=
  rfl
