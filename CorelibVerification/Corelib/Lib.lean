import CorelibVerification.Corelib.Array

open Sierra

aegis_spec "core::panic_with_felt252" :=
  fun _ a ρ =>
  ρ = .inr ((), [a])

aegis_prove "core::panic_with_felt252" :=
  fun _ a ρ => by
  unfold «spec_core::panic_with_felt252»
  aesop

aegis_spec "core::Felt252Sub::sub" :=
  fun _ a b ρ =>
  ρ = a - b

aegis_prove "core::Felt252Sub::sub" :=
  fun _ a b ρ => by
  rintro rfl
  rfl

aegis_spec "core::Felt252PartialEq::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "core::Felt252PartialEq::eq" :=
  fun _ a b ρ => by
  unfold «spec_core::Felt252PartialEq::eq»
  rintro (⟨h,rfl⟩|h)
  · aesop (add forward safe eq_of_sub_eq_zero)
  · aesop

aegis_spec "core::BoolNot::not" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool (¬ a)

aegis_prove "core::BoolNot::not" :=
  fun _ a ρ => by
  rintro rfl
  unfold «spec_core::BoolNot::not»
  simp

aegis_spec "core::Felt252PartialEq::ne" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a ≠ b)

aegis_prove "core::Felt252PartialEq::ne" :=
  fun _ a b ρ => by
  unfold «spec_core::Felt252PartialEq::ne»
  aesop
