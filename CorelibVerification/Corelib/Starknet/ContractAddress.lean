import CorelibVerification.Load
import CorelibVerification.Corelib.Serde

namespace Sierra

aegis_spec "core::starknet::contract_address::Felt252TryIntoContractAddress::try_into" :=
  fun _ _ a _ ρ =>
  a.val < CONTRACT_ADDRESS_MOD ∧ ρ = .inl a.cast ∨ CONTRACT_ADDRESS_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "core::starknet::contract_address::Felt252TryIntoContractAddress::try_into" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::contract_address::Felt252TryIntoContractAddress::try_into»
  rintro (⟨h,rfl⟩|⟨h,rfl⟩)
  · left
    simp only [h, and_self]
  · right
    simp only [h, and_self]

aegis_spec "core::starknet::contract_address::ContractAddressSerde::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ [a.cast]

aegis_prove "core::starknet::contract_address::ContractAddressSerde::serialize" :=
  fun _ a b ρ => by
  unfold «spec_core::starknet::contract_address::ContractAddressSerde::serialize»
  intro
  simp_all only [and_true]

aegis_spec "core::starknet::contract_address::ContractAddressSerde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < CONTRACT_ADDRESS_MOD)).map ZMod.cast).toSum

aegis_prove "core::starknet::contract_address::ContractAddressSerde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::starknet::contract_address::ContractAddressSerde::deserialize»
  aesop (add simp [Option.inl_eq_toSum_iff, Option.inr_eq_toSum_iff])

aegis_spec "core::option::OptionTraitImpl<core::starknet::contract_address::ContractAddress>::expect" :=
  fun _ a b ρ =>
  ρ = a.map id fun _ => ((), [b])

aegis_prove "core::option::OptionTraitImpl<core::starknet::contract_address::ContractAddress>::expect" :=
  fun _ a b ρ => by
  unfold «spec_core::option::OptionTraitImpl<core::starknet::contract_address::ContractAddress>::expect»
  aesop

aegis_spec "core::starknet::contract_address::ContractAddressIntoFelt252::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "core::starknet::contract_address::ContractAddressIntoFelt252::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl
