import CorelibVerification.Load

namespace Sierra

aegis_spec "core::starknet::contract_address::Felt252TryIntoContractAddress::try_into" :=
  fun _ _ a _ ρ => 
  a.val < CONTRACT_ADDRESS_MOD ∧ ρ = .inl a ∨ CONTRACT_ADDRESS_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "core::starknet::contract_address::Felt252TryIntoContractAddress::try_into" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::starknet::contract_address::Felt252TryIntoContractAddress::try_into»
  rintro (⟨h,rfl⟩|⟨h,rfl⟩)
  · left
    simp only [h, and_self]
  · right
    simp only [h, and_self]
