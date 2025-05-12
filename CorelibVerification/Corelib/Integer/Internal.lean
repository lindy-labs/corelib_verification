import CorelibVerification.Corelib.Integer.Traits

open Sierra

aegis_spec "core::internal::InferDestructDestruct<core::integer::u128, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>::destruct" :=
  fun _ _ =>
  True

aegis_prove "core::internal::InferDestructDestruct<core::integer::u128, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>::destruct" :=
  fun _ _ h => h
