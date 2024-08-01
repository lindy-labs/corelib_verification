import CorelibVerification.Load

aegis_spec "core::metaprogramming::TupleSplitTupleSize1<core::integer::u32>::split_head" :=
  fun _ a ρ =>
  ρ = (a, ())

aegis_prove "core::metaprogramming::TupleSplitTupleSize1<core::integer::u32>::split_head" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::metaprogramming::TupleSplitTupleSize1<core::starknet::contract_address::ContractAddress>::split_head" :=
  fun _ a ρ =>
  ρ = (a, ())

aegis_prove "core::metaprogramming::TupleSplitTupleSize1<core::starknet::contract_address::ContractAddress>::split_head" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::metaprogramming::TupleSplitTupleSize1<core::integer::u64>::split_head" :=
  fun _ a ρ =>
  ρ = (a, ())

aegis_prove "core::metaprogramming::TupleSplitTupleSize1<core::integer::u64>::split_head" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::metaprogramming::TupleSplitTupleSize2<core::integer::u32, core::integer::u32>::split_head" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::metaprogramming::TupleSplitTupleSize2<core::integer::u32, core::integer::u32>::split_head" :=
  fun _ a ρ => by
  unfold «spec_core::metaprogramming::TupleSplitTupleSize2<core::integer::u32, core::integer::u32>::split_head»
  aesop

aegis_spec "core::metaprogramming::TupleSplitTupleSize2<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress>::split_head" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::metaprogramming::TupleSplitTupleSize2<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress>::split_head" :=
  fun _ a ρ => by
  unfold «spec_core::metaprogramming::TupleSplitTupleSize2<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress>::split_head»
  aesop

aegis_spec "core::metaprogramming::TupleSplitTupleSize2<core::starknet::contract_address::ContractAddress, core::integer::u64>::split_head" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::metaprogramming::TupleSplitTupleSize2<core::starknet::contract_address::ContractAddress, core::integer::u64>::split_head" :=
  fun _ a ρ => by
  unfold «spec_core::metaprogramming::TupleSplitTupleSize2<core::starknet::contract_address::ContractAddress, core::integer::u64>::split_head»
  aesop

aegis_spec "core::metaprogramming::TupleSplitTupleSize2<core::integer::u32, core::integer::u64>::split_head" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::metaprogramming::TupleSplitTupleSize2<core::integer::u32, core::integer::u64>::split_head" :=
  fun _ a ρ => by
  unfold «spec_core::metaprogramming::TupleSplitTupleSize2<core::integer::u32, core::integer::u64>::split_head»
  aesop
