import CorelibVerification.Load

aegis_spec "core::starknet::use_system_implicit" :=
  fun _ s s' _ =>
  s' = s

aegis_prove "core::starknet::use_system_implicit" :=
  fun _ s s' _ => by
  rintro ⟨rfl,-⟩
  rfl
