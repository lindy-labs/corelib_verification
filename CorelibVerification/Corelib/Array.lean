import CorelibVerification.Load

aegis_spec "core::array::ArrayImpl<core::felt252>::append" :=
  fun _ a b ρ _ =>
  ρ = a ++ [b]

aegis_prove "core::array::ArrayImpl<core::felt252>::append" :=
  fun _ a b ρ _ => by
  aesop
