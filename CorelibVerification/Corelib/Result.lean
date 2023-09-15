import CorelibVerification.Load

aegis_spec "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::expect<core::integer::u32Drop>" :=
  fun _ a _ ρ =>
  (∃ b, a = .inl b ∧ ρ = .inl b) ∨ (a.isRight ∧ ρ.isRight)

aegis_prove "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::expect<core::integer::u32Drop>" :=
  fun _ a _ ρ => by
  unfold «spec_core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::expect<core::integer::u32Drop>»
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u64, core::integer::u64>::expect<core::integer::u64Drop>" :=
  fun _ a _ ρ =>
  (∃ b, a = .inl b ∧ ρ = .inl b) ∨ (a.isRight ∧ ρ.isRight)

aegis_prove "core::result::ResultTraitImpl<core::integer::u64, core::integer::u64>::expect<core::integer::u64Drop>" :=
  fun _ a _ ρ => by
  unfold «spec_core::result::ResultTraitImpl<core::integer::u64, core::integer::u64>::expect<core::integer::u64Drop>»
  aesop
