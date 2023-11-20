import CorelibVerification.Load

namespace Aegis

aegis_spec "core::hash::LegacyHashContractAddress::hash" := fun m _ a b _ ρ =>
  ρ = m.pedersen a b.cast

aegis_prove "core::hash::LegacyHashContractAddress::hash" := fun m _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::LegacyHashU32::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen a b.cast

aegis_prove "core::hash::LegacyHashU32::hash" :=
  fun m _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::LegacyHashU64::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen a b.cast

aegis_prove "core::hash::LegacyHashU64::hash" :=
  fun m _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::TupleSize2LegacyHash<core::starknet::contract_address::ContractAddress, core::integer::u64, core::hash::LegacyHashContractAddress, core::hash::LegacyHashU64, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2LegacyHash<core::starknet::contract_address::ContractAddress, core::integer::u64, core::hash::LegacyHashContractAddress, core::hash::LegacyHashU64, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2LegacyHash<core::starknet::contract_address::ContractAddress, core::integer::u64, core::hash::LegacyHashContractAddress, core::hash::LegacyHashU64, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  aesop

aegis_spec "core::hash::TupleSize2LegacyHash<core::integer::u32, core::integer::u64, core::hash::LegacyHashU32, core::hash::LegacyHashU64, core::integer::u32Drop, core::integer::u64Drop>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2LegacyHash<core::integer::u32, core::integer::u64, core::hash::LegacyHashU32, core::hash::LegacyHashU64, core::integer::u32Drop, core::integer::u64Drop>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2LegacyHash<core::integer::u32, core::integer::u64, core::hash::LegacyHashU32, core::hash::LegacyHashU64, core::integer::u32Drop, core::integer::u64Drop>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  aesop

aegis_spec "core::hash::TupleSize2LegacyHash<core::integer::u32, core::integer::u32, core::hash::LegacyHashU32, core::hash::LegacyHashU32, core::integer::u32Drop, core::integer::u32Drop>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2LegacyHash<core::integer::u32, core::integer::u32, core::hash::LegacyHashU32, core::hash::LegacyHashU32, core::integer::u32Drop, core::integer::u32Drop>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2LegacyHash<core::integer::u32, core::integer::u32, core::hash::LegacyHashU32, core::hash::LegacyHashU32, core::integer::u32Drop, core::integer::u32Drop>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  aesop

aegis_spec "core::hash::TupleSize2LegacyHash<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::hash::LegacyHashContractAddress, core::hash::LegacyHashContractAddress, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2LegacyHash<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::hash::LegacyHashContractAddress, core::hash::LegacyHashContractAddress, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2LegacyHash<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::hash::LegacyHashContractAddress, core::hash::LegacyHashContractAddress, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  aesop
