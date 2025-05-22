import CorelibVerification.Corelib.Integer.Traits

aegis_spec "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::into_is_err<core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool a.isRight

aegis_prove "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::into_is_err<core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>" :=
  fun _ a ρ => by
  unfold_spec "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::into_is_err<core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>"
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::into_is_ok<core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool a.isLeft

aegis_prove "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::into_is_ok<core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>" :=
  fun _ a ρ => by
  unfold_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::into_is_ok<core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>"
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::into_is_ok<core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool a.isLeft

aegis_prove "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::into_is_ok<core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>" :=
  fun _ a ρ => by
  unfold_spec "core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::into_is_ok<core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>"
  aesop
