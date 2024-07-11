import CorelibVerification.Corelib.Lib

aegis_spec "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::expect<core::integer::u32Drop>" :=
  fun _ a _ ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::expect<core::integer::u32Drop>" :=
  fun _ a _ ρ => by
  unfold «spec_core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::expect<core::integer::u32Drop>»
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u64, core::integer::u64>::expect<core::integer::u64Drop>" :=
  fun _ a _ ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::result::ResultTraitImpl<core::integer::u64, core::integer::u64>::expect<core::integer::u64Drop>" :=
  fun _ a _ ρ => by
  unfold «spec_core::result::ResultTraitImpl<core::integer::u64, core::integer::u64>::expect<core::integer::u64Drop>»
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::into_is_err<core::integer::u128Drop, core::integer::u128Drop>" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool a.isRight

aegis_prove "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::into_is_err<core::integer::u128Drop, core::integer::u128Drop>" :=
  fun _ a ρ => by
  unfold «spec_core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::into_is_err<core::integer::u128Drop, core::integer::u128Drop>»
  aesop
