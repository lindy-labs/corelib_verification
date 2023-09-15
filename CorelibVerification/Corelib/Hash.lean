import CorelibVerification.Load

namespace Aegis

aegis_spec "core::hash::LegacyHashContractAddress::hash" := fun m _ a b _ ρ =>
  ρ = m.pedersen a b.cast

aegis_prove "core::hash::LegacyHashContractAddress::hash" := fun m _ a b _ ρ => by
  rintro rfl
  rfl
