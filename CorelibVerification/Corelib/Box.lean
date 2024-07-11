import CorelibVerification.Load

open Sierra

aegis_spec "core::box::BoxImpl<core::integer::u64>::unbox" :=
  fun m a ρ =>
  (m.boxHeap .U64 a) = .some ρ

aegis_prove "core::box::BoxImpl<core::integer::u64>::unbox" :=
  fun m a ρ => by
  unfold «spec_core::box::BoxImpl<core::integer::u64>::unbox»
  aesop

aegis_spec "core::box::BoxImpl<core::felt252>::unbox" :=
  fun m a ρ =>
  (m.boxHeap .Felt252 a) = .some ρ

aegis_prove "core::box::BoxImpl<core::felt252>::unbox" :=
  fun m a ρ => by
  unfold «spec_core::box::BoxImpl<core::felt252>::unbox»
  aesop

aegis_spec "core::box::BoxImpl<core::integer::u128>::unbox" :=
  fun m a ρ =>
  (m.boxHeap .U128 a) = .some ρ

aegis_prove "core::box::BoxImpl<core::integer::u128>::unbox" :=
  fun m a ρ => by
  unfold «spec_core::box::BoxImpl<core::integer::u128>::unbox»
  aesop

aegis_spec "core::box::BoxImpl<core::starknet::info::v2::ExecutionInfo>::unbox" :=
  fun m a ρ =>
  (m.boxHeap .V2ExecutionInfo a) = .some ρ

aegis_prove "core::box::BoxImpl<core::starknet::info::v2::ExecutionInfo>::unbox" :=
  fun m a ρ => by
  unfold «spec_core::box::BoxImpl<core::starknet::info::v2::ExecutionInfo>::unbox»
  aesop

aegis_spec "core::box::BoxImpl<core::starknet::info::BlockInfo>::unbox" :=
  fun m a ρ =>
  (m.boxHeap .BlockInfo a) = .some ρ

aegis_prove "core::box::BoxImpl<core::starknet::info::BlockInfo>::unbox" :=
  fun m a ρ => by
  unfold «spec_core::box::BoxImpl<core::starknet::info::BlockInfo>::unbox»
  aesop
