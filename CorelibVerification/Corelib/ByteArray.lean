import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.Bytes31

aegis_spec "core::byte_array::ByteArrayDefault::default" :=
  fun _ ρ =>
  ρ = ([], 0, 0)

aegis_prove "core::byte_array::ByteArrayDefault::default" :=
  fun _ ρ => by
  rintro rfl
  rfl
