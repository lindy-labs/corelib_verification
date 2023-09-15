import AuraContractsVerification.Load
import AuraContractsVerification.Corelib.Serde

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

aegis_spec "core::starknet::contract_address::ContractAddressSerde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::starknet::contract_address::ContractAddressSerde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::starknet::contract_address::ContractAddressSerde::serialize»
  intro
  simp_all only [and_true]

aegis_spec "core::serde::serialize_array_helper<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddressSerde, core::starknet::contract_address::ContractAddressDrop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::serde::serialize_array_helper<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddressSerde, core::starknet::contract_address::ContractAddressDrop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data.map ZMod.cast, ())
  else ρ.isRight

aegis_prove "core::serde::serialize_array_helper<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddressSerde, core::starknet::contract_address::ContractAddressDrop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::serde::serialize_array_helper<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddressSerde, core::starknet::contract_address::ContractAddressDrop>»
  sierra_simp'
  set c := m.costs id!"core::serde::serialize_array_helper<core::starknet::contract_address::ContractAddress, core::starknet::contract_address::ContractAddressSerde, core::starknet::contract_address::ContractAddressDrop>"
  rintro (⟨hle,h⟩|⟨h,rfl⟩)
  · rcases h with (⟨a,b,_,d,e,rfl,h₁,h₂,h₃⟩|⟨rfl,rfl,rfl⟩)
    · injection h₁ with h₁; subst h₁
      split_ifs at h₂ with hle'
      · rcases h₂ with ⟨rfl,rfl⟩
        have : (a.length + 2) * c ≤ gas
        · have := Nat.add_le_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.append_assoc, List.singleton_append, Sum.inl.injEq, ge_iff_le,
          tsub_le_iff_right, exists_and_left, exists_and_right, exists_eq_left, Prod.mk.injEq,
          and_true, exists_const, false_and, exists_false, or_false] at h₃
        rcases h₃ with ⟨rfl,rfl⟩ 
        simp only [List.length_cons, this, ge_iff_le, tsub_le_iff_right, and_true, Sum.isRight_inl,
          ite_true]
        rw [add_mul, one_mul, add_mul, Nat.succ_mul, one_mul, Nat.sub_sub]
        simp only [List.map_cons, and_true]
        ac_rfl
      · have : ¬ (a.length + 2) * c ≤ gas
        · rw [not_le] at hle' ⊢
          have := Nat.add_lt_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.length_cons, this, ge_iff_le, ite_false]
        aesop
    · simp [hle]
  · have : ¬ (data.length + 1) * c ≤ gas
    · rw [not_le, Nat.add_mul, one_mul]; apply Nat.lt_add_left h
    simp [this]
