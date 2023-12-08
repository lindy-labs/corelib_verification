import CorelibVerification.Load

aegis_spec "core::pedersen::HashStateImpl::update" :=
  fun m _ hs a _ ρ =>
  ρ = m.pedersen hs a

aegis_prove "core::pedersen::HashStateImpl::update" :=
  fun m _ hs a _ ρ => by
  unfold «spec_core::pedersen::HashStateImpl::update»
  aesop
