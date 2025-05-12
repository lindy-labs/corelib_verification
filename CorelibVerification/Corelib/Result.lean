import CorelibVerification.Corelib.Lib
import CorelibVerification.Corelib.Integer.Traits

aegis_spec "core::result::ResultTraitImpl::<core::integer::u32, core::integer::u32>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u32, core::traits::DestructFromDrop::<core::integer::u32, core::integer::u32Drop>>>" :=
  fun _ a _ ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::result::ResultTraitImpl::<core::integer::u32, core::integer::u32>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u32, core::traits::DestructFromDrop::<core::integer::u32, core::integer::u32Drop>>>" :=
  fun _ a _ ρ => by
  unfold_spec "core::result::ResultTraitImpl::<core::integer::u32, core::integer::u32>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u32, core::traits::DestructFromDrop::<core::integer::u32, core::integer::u32Drop>>>"
  aesop

aegis_spec "core::result::ResultTraitImpl::<core::integer::u64, core::integer::u64>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u64, core::traits::DestructFromDrop::<core::integer::u64, core::integer::u64Drop>>>" :=
  fun _ a _ ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::result::ResultTraitImpl::<core::integer::u64, core::integer::u64>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u64, core::traits::DestructFromDrop::<core::integer::u64, core::integer::u64Drop>>>" :=
  fun _ a _ ρ => by
  unfold_spec "core::result::ResultTraitImpl::<core::integer::u64, core::integer::u64>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u64, core::traits::DestructFromDrop::<core::integer::u64, core::integer::u64Drop>>>"
  aesop

aegis_spec "core::result::ResultTraitImpl::<core::integer::u16, core::integer::u16>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u16, core::traits::DestructFromDrop::<core::integer::u16, core::integer::u16Drop>>>" :=
  fun _ a err ρ =>
  a.isLeft ∧ ρ = .inl a.getLeft?.get! ∨
    a.isRight ∧ ρ = .inr ((), [err])

aegis_prove "core::result::ResultTraitImpl::<core::integer::u16, core::integer::u16>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u16, core::traits::DestructFromDrop::<core::integer::u16, core::integer::u16Drop>>>" :=
  fun _ a err ρ => by
  unfold_spec "core::result::ResultTraitImpl::<core::integer::u16, core::integer::u16>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u16, core::traits::DestructFromDrop::<core::integer::u16, core::integer::u16Drop>>>"
  aesop

aegis_spec "core::result::ResultTraitImpl::<core::integer::u8, core::integer::u8>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u8, core::traits::DestructFromDrop::<core::integer::u8, core::integer::u8Drop>>>" :=
  fun _ a err ρ =>
  a.isLeft ∧ ρ = .inl a.getLeft?.get! ∨
    a.isRight ∧ ρ = .inr ((), [err])

aegis_prove "core::result::ResultTraitImpl::<core::integer::u8, core::integer::u8>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u8, core::traits::DestructFromDrop::<core::integer::u8, core::integer::u8Drop>>>" :=
  fun _ a err ρ => by
  unfold_spec "core::result::ResultTraitImpl::<core::integer::u8, core::integer::u8>::expect::<core::traits::PanicDestructForDestruct::<core::integer::u8, core::traits::DestructFromDrop::<core::integer::u8, core::integer::u8Drop>>>"
  aesop

aegis_spec "core::result::ResultTraitImpl::<core::integer::u128, core::integer::u128>::into_is_err::<core::traits::DestructFromDrop::<core::integer::u128, core::integer::u128Drop>, core::traits::DestructFromDrop::<core::integer::u128, core::integer::u128Drop>>" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool a.isRight

aegis_prove "core::result::ResultTraitImpl::<core::integer::u128, core::integer::u128>::into_is_err::<core::traits::DestructFromDrop::<core::integer::u128, core::integer::u128Drop>, core::traits::DestructFromDrop::<core::integer::u128, core::integer::u128Drop>>" :=
  fun _ a ρ => by
  unfold_spec "core::result::ResultTraitImpl::<core::integer::u128, core::integer::u128>::into_is_err::<core::traits::DestructFromDrop::<core::integer::u128, core::integer::u128Drop>, core::traits::DestructFromDrop::<core::integer::u128, core::integer::u128Drop>>"
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::traits::PanicDestructForDestruct<core::integer::u128, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>>" :=
  fun _ a err ρ =>
  a.isLeft ∧ ρ = .inl a.getLeft?.get! ∨
    a.isRight ∧ ρ = .inr ((), [err])

aegis_prove "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::traits::PanicDestructForDestruct<core::integer::u128, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>>" :=
  fun _ a err ρ => by
  unfold_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::traits::PanicDestructForDestruct<core::integer::u128, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>>"
  aesop
