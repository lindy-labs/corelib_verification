import CorelibVerification.Corelib.Pedersen

namespace Aegis

aegis_spec "core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>::update_state" :=
  fun m _ hs a _ ρ =>
  ρ = m.pedersen hs a.cast

aegis_prove "core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>::update_state" :=
  fun m _ hs a _ ρ => by
  unfold «spec_core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>::update_state»
  rintro rfl
  rfl

aegis_spec "core::hash::LegacyHashForHash::<core::starknet::contract_address::ContractAddress, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen a b.cast

aegis_prove "core::hash::LegacyHashForHash::<core::starknet::contract_address::ContractAddress, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>>::hash" :=
  fun m _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>::update_state" :=
  fun m _ hs a _ ρ =>
  ρ = m.pedersen hs a.cast

aegis_prove "core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>::update_state" :=
  fun m _ hs a _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::LegacyHashForHash::<core::integer::u32, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen a b.cast

aegis_prove "core::hash::LegacyHashForHash::<core::integer::u32, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>>::hash" :=
  fun m _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>::update_state" :=
  fun m _ hs a _ ρ =>
  ρ = m.pedersen hs a.cast

aegis_prove "core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>::update_state" :=
  fun m _ hs a _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::LegacyHashForHash::<core::integer::u64, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen a b.cast

aegis_prove "core::hash::LegacyHashForHash::<core::integer::u64, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>>::hash" :=
  fun m _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::hash::TupleSize2Hash<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>::update_state" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2Hash<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>::update_state" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2Hash<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>::update_state»
  aesop

aegis_spec "core::hash::LegacyHashForHash::<(core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress), core::hash::TupleSize2Hash::<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::LegacyHashForHash::<(core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress), core::hash::TupleSize2Hash::<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::LegacyHashForHash::<(core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress), core::hash::TupleSize2Hash::<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::starknet::contract_address::ContractAddressDrop>>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  rfl

aegis_spec "core::hash::TupleSize2Hash<core::integer::u32, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u64Drop>::update_state" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2Hash<core::integer::u32, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u64Drop>::update_state" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2Hash<core::integer::u32, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u64Drop>::update_state»
  rintro ⟨_,_,rfl,rfl⟩
  rfl

aegis_spec "core::hash::LegacyHashForHash::<(core::integer::u32, core::integer::u64), core::hash::TupleSize2Hash::<core::integer::u32, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u64Drop>>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::LegacyHashForHash::<(core::integer::u32, core::integer::u64), core::hash::TupleSize2Hash::<core::integer::u32, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u64Drop>>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::LegacyHashForHash::<(core::integer::u32, core::integer::u64), core::hash::TupleSize2Hash::<core::integer::u32, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u64Drop>>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  rfl

aegis_spec "core::hash::TupleSize2Hash<core::integer::u32, core::integer::u32, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u32Drop>::update_state" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2Hash<core::integer::u32, core::integer::u32, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u32Drop>::update_state" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2Hash<core::integer::u32, core::integer::u32, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u32Drop>::update_state»
  rintro ⟨_,_,rfl,rfl⟩
  rfl

aegis_spec "core::hash::LegacyHashForHash::<(core::integer::u32, core::integer::u32), core::hash::TupleSize2Hash::<core::integer::u32, core::integer::u32, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u32Drop>>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::LegacyHashForHash::<(core::integer::u32, core::integer::u32), core::hash::TupleSize2Hash::<core::integer::u32, core::integer::u32, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u32Drop>>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::LegacyHashForHash::<(core::integer::u32, core::integer::u32), core::hash::TupleSize2Hash::<core::integer::u32, core::integer::u32, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u32, core::pedersen::HashState, core::integer::U32IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::integer::u32Drop, core::integer::u32Drop>>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  rfl

aegis_spec "core::hash::TupleSize2Hash<core::starknet::contract_address::ContractAddress, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>::update_state" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::TupleSize2Hash<core::starknet::contract_address::ContractAddress, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>::update_state" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::TupleSize2Hash<core::starknet::contract_address::ContractAddress, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>::update_state»
  rintro ⟨_,_,rfl,rfl⟩
  rfl

aegis_spec "core::hash::LegacyHashForHash::<(core::starknet::contract_address::ContractAddress, core::integer::u64), core::hash::TupleSize2Hash::<core::starknet::contract_address::ContractAddress, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>>::hash" :=
  fun m _ a b _ ρ =>
  ρ = m.pedersen (m.pedersen a b.1.cast) b.2.cast

aegis_prove "core::hash::LegacyHashForHash::<(core::starknet::contract_address::ContractAddress, core::integer::u64), core::hash::TupleSize2Hash::<core::starknet::contract_address::ContractAddress, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>>::hash" :=
  fun m _ a b _ ρ => by
  unfold «spec_core::hash::LegacyHashForHash::<(core::starknet::contract_address::ContractAddress, core::integer::u64), core::hash::TupleSize2Hash::<core::starknet::contract_address::ContractAddress, core::integer::u64, core::pedersen::HashState, core::pedersen::HashStateImpl, core::hash::into_felt252_based::HashImpl::<core::starknet::contract_address::ContractAddress, core::pedersen::HashState, core::starknet::contract_address::ContractAddressIntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::hash::into_felt252_based::HashImpl::<core::integer::u64, core::pedersen::HashState, core::integer::U64IntoFelt252, core::pedersen::HashStateImpl, core::pedersen::HashStateDrop>, core::starknet::contract_address::ContractAddressDrop, core::integer::u64Drop>>::hash»
  rintro ⟨_,_,rfl,rfl⟩
  rfl
