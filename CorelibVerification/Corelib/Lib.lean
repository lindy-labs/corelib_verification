import CorelibVerification.Corelib.Array

aegis_spec "core::panic_with_felt252" :=
  fun _ a ρ =>
  ρ = .inr ((), [a])

aegis_prove "core::panic_with_felt252" :=
  fun _ a ρ => by
  unfold «spec_core::panic_with_felt252»
  aesop

aegis_spec "core::Felt252PartialEq::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_spec "core::Felt252PartialEq::ne" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a ≠ b)

aegis_prove "core::Felt252PartialEq::ne" :=
  fun _ a b ρ => by
  unfold «spec_core::Felt252PartialEq::ne»
  aesop
