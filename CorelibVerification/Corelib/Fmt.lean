import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.ByteArray

aegis_spec "core::fmt::FormatterDefault::default" :=
  fun _ ρ =>
  ρ = ([], 0, 0)

aegis_prove "core::fmt::FormatterDefault::default" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>::destruct" :=
  fun _ _ =>
  True

aegis_prove "core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>::destruct" :=
  fun _ _ _ => True.intro

aegis_spec "core::traits::PanicDestructForDestruct<core::fmt::Error, core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>::panic_destruct" :=
  fun _ _ _ ρ =>
  ρ = ()

aegis_prove "core::traits::PanicDestructForDestruct<core::fmt::Error, core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>::panic_destruct" :=
  fun _ _ _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::result::ResultTraitImpl<(), core::fmt::Error>::expect<core::traits::PanicDestructForDestruct<core::fmt::Error, core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>>" :=
  fun _ a err ρ =>
  a.isLeft ∧ ρ = .inl () ∨
    a.isRight ∧ ρ = .inr ((), [err])

aegis_prove "core::result::ResultTraitImpl<(), core::fmt::Error>::expect<core::traits::PanicDestructForDestruct<core::fmt::Error, core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>>" :=
  fun _ a err ρ => by
  unfold_spec "core::result::ResultTraitImpl<(), core::fmt::Error>::expect<core::traits::PanicDestructForDestruct<core::fmt::Error, core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>>"
  aesop

aegis_spec "core::result::ResultTraitImpl<(), core::fmt::Error>::unwrap<core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>" :=
  fun _ a ρ =>
  a = .inl () ∧ ρ = .inl () ∨
    a = .inr () ∧ ρ.isRight

aegis_prove "core::result::ResultTraitImpl<(), core::fmt::Error>::unwrap<core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>" :=
  fun _ a ρ => by
  unfold_spec "core::result::ResultTraitImpl<(), core::fmt::Error>::unwrap<core::traits::DestructFromDrop<core::fmt::Error, core::fmt::ErrorDrop>>"
  aesop
