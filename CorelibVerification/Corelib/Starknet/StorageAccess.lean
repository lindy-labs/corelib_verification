import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.Starknet.ContractAddress
import CorelibVerification.Aux.Bool
import CorelibVerification.Aux.PanicResult
import CorelibVerification.Load

namespace Sierra

aegis_spec "core::starknet::storage_access::StoreFelt252::read" :=
  fun m _ s _ b_add _ s' ρ =>
  let r := (s.contracts m.contractAddress.cast).storage b_add.cast
  s' = s ∧ (ρ = .inl r ∨ ρ.isRight)

aegis_prove "core::starknet::storage_access::StoreFelt252::read" :=
  fun m _ s _ b_add _ s' ρ => by
  unfold «spec_core::starknet::storage_access::StoreFelt252::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreU8::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) =>
  let r := (s.contracts m.contractAddress.cast).storage b_add.cast
  s' = s
  ∧ (r.val < U8_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U8_MOD ≤ r.val ∧ ρ.fails
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreU8::read" :=
  fun m _ _ s _ b_add _ _ s' ρ => by
  unfold «spec_core::starknet::storage_access::StoreU8::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreU16::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) =>
  let r := (s.contracts m.contractAddress.cast).storage b_add.cast
  s' = s
  ∧ (r.val < U16_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U16_MOD ≤ r.val ∧ ρ.fails
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreU16::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) => by
  unfold «spec_core::starknet::storage_access::StoreU16::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreU32::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) =>
  let r := (s.contracts m.contractAddress.cast).storage b_add.cast
  s' = s
  ∧ (r.val < U32_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U32_MOD ≤ r.val ∧ ρ.fails
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreU32::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) => by
  unfold «spec_core::starknet::storage_access::StoreU32::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreU64::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) =>
  let r := (s.contracts m.contractAddress.cast).storage b_add.cast
  s' = s
  ∧ (r.val < U64_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U64_MOD ≤ r.val ∧ ρ.fails
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreU64::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) => by
  unfold «spec_core::starknet::storage_access::StoreU64::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreU128::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) =>
  let r := (s.contracts m.contractAddress.cast).storage b_add.cast
  s' = s
  ∧ (r.val < U128_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U128_MOD ≤ r.val ∧ ρ.fails
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreU128::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) => by
  unfold «spec_core::starknet::storage_access::StoreU128::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreContractAddress::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) =>
  let r := (s.contracts m.contractAddress.cast).storage b_add.cast
  s' = s
  ∧ (r.val < CONTRACT_ADDRESS_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ CONTRACT_ADDRESS_MOD ≤ r.val ∧ ρ.fails
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StoreContractAddress::read" :=
  fun m _ _ s _ b_add _ _ s' (ρ : PanicResult _) => by
  unfold «spec_core::starknet::storage_access::StoreContractAddress::read»
  aesop

aegis_spec "core::starknet::storage_access::StoreBool::read" :=
  fun m _ s _ b_addr _ s' ρ =>
  let r := (s.contracts m.contractAddress.cast).storage b_addr.cast
  s' = s
  ∧ (ρ = .inl (Bool.toSierraBool (r ≠ 0)) ∨ ρ.isRight)

aegis_prove "core::starknet::storage_access::StoreBool::read" :=
  fun m _ s _ b_addr _ s' ρ => by
  unfold «spec_core::starknet::storage_access::StoreBool::read»
  simp only [StorageAddress, ADDRESS_MOD]
  aesop
