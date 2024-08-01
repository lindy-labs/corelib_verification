import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.Starknet.ContractAddress
import CorelibVerification.Aux.Bool
import CorelibVerification.Load

namespace Sierra

aegis_spec "core::starknet::storage_access::StoreFelt252::read" :=
  fun m _ sys _ b_add _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress.cast).storage b_add.cast
  ρ_sys = sys ∧ (ρ = .inl r ∨ ρ.isRight)

aegis_prove "core::starknet::storage_access::StoreFelt252::read" :=
  fun m _ sys _ b_add _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StoreFelt252::read»
  aesop

aegis_spec "core::starknet::storage_access::StorePackingContractAddress::unpack" :=
  fun _ _ a _ ρ =>
  a.val < CONTRACT_ADDRESS_MOD ∧ ρ = .inl a.cast
  ∨ CONTRACT_ADDRESS_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::starknet::storage_access::StorePackingContractAddress::unpack" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::storage_access::StorePackingContractAddress::unpack»
  aesop

aegis_spec "core::starknet::storage_access::StorePackingBool::unpack" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool (a ≠ 0)

aegis_prove "core::starknet::storage_access::StorePackingBool::unpack" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::starknet::storage_access::StorePackingU128::unpack" :=
  fun _ _ a _ ρ =>
  a.val < U128_MOD ∧ ρ = .inl a.cast
  ∨ U128_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::starknet::storage_access::StorePackingU128::unpack" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::storage_access::StorePackingU128::unpack»
  aesop

aegis_spec "core::starknet::storage_access::StorePackingU64::unpack" :=
  fun _ _ a _ ρ =>
  a.val < U64_MOD ∧ ρ = .inl a.cast
  ∨ U64_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::starknet::storage_access::StorePackingU64::unpack" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::storage_access::StorePackingU64::unpack»
  aesop

aegis_spec "core::starknet::storage_access::StorePackingU32::unpack" :=
  fun _ _ a _ ρ =>
  a.val < U32_MOD ∧ ρ = .inl a.cast
  ∨ U32_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::starknet::storage_access::StorePackingU32::unpack" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::storage_access::StorePackingU32::unpack»
  aesop

aegis_spec "core::starknet::storage_access::StorePackingU16::unpack" :=
  fun _ _ a _ ρ =>
  a.val < U16_MOD ∧ ρ = .inl a.cast
  ∨ U16_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::starknet::storage_access::StorePackingU16::unpack" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::storage_access::StorePackingU16::unpack»
  aesop

aegis_spec "core::starknet::storage_access::StorePackingU8::unpack" :=
  fun _ _ a _ ρ =>
  a.val < U8_MOD ∧ ρ = .inl a.cast
  ∨ U8_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::starknet::storage_access::StorePackingU8::unpack" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::storage_access::StorePackingU8::unpack»
  aesop

aegis_spec "core::starknet::storage_access::StoreUsingPacking<core::integer::u8, core::felt252, core::starknet::storage_access::StorePackingU8, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress.cast).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U8_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U8_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreUsingPacking<core::integer::u8, core::felt252, core::starknet::storage_access::StorePackingU8, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StoreUsingPacking<core::integer::u8, core::felt252, core::starknet::storage_access::StorePackingU8, core::starknet::storage_access::StoreFelt252>::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreUsingPacking<core::integer::u16, core::felt252, core::starknet::storage_access::StorePackingU16, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress.cast).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U16_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U16_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreUsingPacking<core::integer::u16, core::felt252, core::starknet::storage_access::StorePackingU16, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StoreUsingPacking<core::integer::u16, core::felt252, core::starknet::storage_access::StorePackingU16, core::starknet::storage_access::StoreFelt252>::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreUsingPacking<core::integer::u32, core::felt252, core::starknet::storage_access::StorePackingU32, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress.cast).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U32_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U32_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreUsingPacking<core::integer::u32, core::felt252, core::starknet::storage_access::StorePackingU32, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StoreUsingPacking<core::integer::u32, core::felt252, core::starknet::storage_access::StorePackingU32, core::starknet::storage_access::StoreFelt252>::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreUsingPacking<core::integer::u64, core::felt252, core::starknet::storage_access::StorePackingU64, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress.cast).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U64_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U64_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreUsingPacking<core::integer::u64, core::felt252, core::starknet::storage_access::StorePackingU64, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StoreUsingPacking<core::integer::u64, core::felt252, core::starknet::storage_access::StorePackingU64, core::starknet::storage_access::StoreFelt252>::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreUsingPacking<core::integer::u128, core::felt252, core::starknet::storage_access::StorePackingU128, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress.cast).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U128_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U128_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreUsingPacking<core::integer::u128, core::felt252, core::starknet::storage_access::StorePackingU128, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StoreUsingPacking<core::integer::u128, core::felt252, core::starknet::storage_access::StorePackingU128, core::starknet::storage_access::StoreFelt252>::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreUsingPacking<core::starknet::contract_address::ContractAddress, core::felt252, core::starknet::storage_access::StorePackingContractAddress, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress.cast).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < CONTRACT_ADDRESS_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ CONTRACT_ADDRESS_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreUsingPacking<core::starknet::contract_address::ContractAddress, core::felt252, core::starknet::storage_access::StorePackingContractAddress, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StoreUsingPacking<core::starknet::contract_address::ContractAddress, core::felt252, core::starknet::storage_access::StorePackingContractAddress, core::starknet::storage_access::StoreFelt252>::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreUsingPacking<core::bool, core::felt252, core::starknet::storage_access::StorePackingBool, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ s _ b_addr _ s' ρ =>
  let r := (s.contracts m.contractAddress.cast).storage b_addr.cast
  s' = s
  ∧ (ρ = .inl (Bool.toSierraBool (r ≠ 0)) ∨ ρ.isRight)

aegis_prove "core::starknet::storage_access::StoreUsingPacking<core::bool, core::felt252, core::starknet::storage_access::StorePackingBool, core::starknet::storage_access::StoreFelt252>::read" :=
  fun m _ s _ b_addr _ s' ρ => by
  unfold «spec_core::starknet::storage_access::StoreUsingPacking<core::bool, core::felt252, core::starknet::storage_access::StorePackingBool, core::starknet::storage_access::StoreFelt252>::read»
  simp only [StorageAddress, ADDRESS_MOD]
  aesop
