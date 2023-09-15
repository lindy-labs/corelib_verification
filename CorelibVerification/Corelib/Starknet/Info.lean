import AuraContractsVerification.Corelib.Starknet.SyscallResult
import AuraContractsVerification.Corelib.Integer

namespace Sierra

aegis_spec "core::starknet::info::get_execution_info" := fun m _ s _ s' ρ =>
  s = s' ∧
  (ρ = .inl ⟨⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩,
    ⟨m.txVersion, m.txContract, m.txMaxFee, m.txSignature, m.txHash, m.txChainIdentifier, m.txNonce⟩,
    m.callerAddress, m.contractAddress, m.entryPointSelector⟩
    ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_execution_info" := fun m _ s _ s' ρ => by
  rintro ⟨_,_,_,_,(⟨h,(⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩|⟨h,(⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩)⟩
    <;> refine ⟨rfl, ?_⟩
  · left
    rcases h with (⟨m',h,h'⟩|⟨h,-⟩)
    · injection h' with h'; cases h'
      injection h with h; cases h
      rfl
    · simp only [Sum.isRight_inl] at h
  · right; apply Sum.isRight_inr
  · left
    rcases h with (⟨m',h,-⟩|⟨-,h'⟩)
    · simp only at h
    · simp only [Sum.isRight_inl] at h'
  · right; apply Sum.isRight_inr

aegis_spec "core::starknet::info::get_caller_address" := fun m _ s _ s' ρ => 
  s = s' ∧ (ρ = .inl m.callerAddress ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_caller_address" := fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_caller_address»
  rintro ⟨_,_,_,_,_,_,_,_,_,rfl,h,(⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩
    <;> aesop

aegis_spec "core::starknet::info::get_block_info" :=
  fun m _ s _ s' ρ =>
  s = s' ∧
  (ρ = .inl ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩ ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_block_info" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_block_info»
  rintro ⟨_,_,_,_,_,_,_,_,_,rfl,(rfl|h),h'⟩
  · rcases h' with (⟨h',rfl,rfl,rfl⟩|h')
    · aesop
    · aesop
  · aesop

aegis_spec "core::starknet::info::get_contract_address" :=
  fun m _ s _ s' ρ =>
  s = s' ∧ (ρ = .inl m.contractAddress ∨ ρ.isRight) 

aegis_prove "core::starknet::info::get_contract_address" := 
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_contract_address»
  rintro ⟨_,_,_,_,_,_,_,_,_,rfl,h,(⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩
  <;> aesop

aegis_spec "core::starknet::info::get_block_timestamp" :=
  fun m _ s _ s' ρ =>
  s = s' ∧ (ρ = .inl m.blockTimestamp ∨ ρ.isRight) 

aegis_prove "core::starknet::info::get_block_timestamp" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_block_timestamp»
  aesop
