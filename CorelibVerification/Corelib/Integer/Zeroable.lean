import CorelibVerification.Corelib.Integer

aegis_spec "core::zeroable::NonZeroIntoImpl<core::integer::u128>::into" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::zeroable::NonZeroIntoImpl<core::integer::u128>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::zeroable::NonZeroPartialEq<core::integer::u128, core::integer::U128PartialEq, core::integer::u128Copy, core::integer::u128Drop>::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "core::zeroable::NonZeroPartialEq<core::integer::u128, core::integer::U128PartialEq, core::integer::u128Copy, core::integer::u128Drop>::eq" :=
  fun _ a b ρ => by
  rintro rfl
  rfl
