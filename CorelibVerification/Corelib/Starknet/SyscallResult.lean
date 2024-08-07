import CorelibVerification.Load

namespace Sierra

aegis_spec "core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u16>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u16>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u16>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall»
  aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::v2::ExecutionInfo>>::unwrap_syscall" :=
  fun _ a ρ =>
  a.isLeft ∧ ρ.isLeft ∧ a.getLeft?.get! = ρ.getLeft?.get!
  ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::v2::ExecutionInfo>>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::v2::ExecutionInfo>>::unwrap_syscall»
  aesop
