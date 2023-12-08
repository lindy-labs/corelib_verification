import CorelibVerification.Corelib.Array

aegis_spec "core::panic_with_felt252" :=
  fun _ a ρ =>
  ρ = .inr ((), [a])

aegis_prove "core::panic_with_felt252" :=
  fun _ a ρ => by
  unfold «spec_core::panic_with_felt252»
  aesop
