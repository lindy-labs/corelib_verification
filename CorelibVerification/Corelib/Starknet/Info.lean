import CorelibVerification.Corelib.Starknet.SyscallResult
import CorelibVerification.Corelib.Integer

namespace Sierra

aegis_spec "core::starknet::info::get_execution_info" :=
  fun m _ s _ s' ρ =>
  s = s' ∧
  ((∃ rei rbi rti, ρ = .inl rei ∧
      m.boxHeap .ExecutionInfo rei = .some ⟨rbi, rti,
      m.callerAddress, m.contractAddress, m.entryPointSelector⟩
      ∧ m.boxHeap .BlockInfo rbi = .some ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩
      ∧ m.boxHeap .TxInfo rti = .some ⟨m.txVersion, m.txContract, m.txMaxFee, m.txSignature,
        m.txHash, m.txChainIdentifier, m.txNonce⟩)
    ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_execution_info" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_execution_info»
  rintro ⟨_,_,_,_,_,(⟨⟨_,_,_,_,_,h₁,h₃,h₄,rfl,rfl,rfl⟩,h₂,h₅⟩|⟨h₁,h₂⟩)⟩
  · simp only [Sum.inl.injEq, exists_eq_left', Sum.isRight_inl, false_and, or_false] at h₂
    subst h₂
    simp only [Sum.inl.injEq, false_and, or_false] at h₅
    rcases h₅ with ⟨rfl,rfl,rfl⟩
    exact ⟨rfl, .inl ⟨_,_,_,rfl,h₁,h₃,h₄⟩⟩
  · simp only [false_and, exists_const, Sum.isRight_inr, true_and, false_or] at h₁
    rcases h₂ with (⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · simp at h₁
    · exact ⟨rfl, .inr rfl⟩

aegis_spec "core::starknet::info::get_caller_address" := fun m _ s _ s' ρ =>
  s = s' ∧ (ρ = .inl m.callerAddress ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_caller_address" := fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_caller_address»
  rintro ⟨_,_,_,_,_,_,_,_,_,_,rfl,h,(⟨rfl,h',rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩
  · simp only [Sum.isRight_inl, or_false] at h
    rcases h with ⟨rei,_,_,h₁,h₂,-,-⟩
    cases h₁
    cases h'.trans h₂
    exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inr rfl⟩

aegis_spec "core::starknet::info::get_block_info" :=
  fun m _ s _ s' ρ =>
  s = s' ∧
  ((∃ rbi,
      m.boxHeap .BlockInfo rbi = .some ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩
      ∧ ρ = .inl rbi)
    ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_block_info" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_block_info»
  rintro ⟨_,_,_,_,_,_,_,_,_,_,rfl,(⟨_,_,_,rfl,h₃,hrbi,-⟩|h₁),h₂⟩
  · simp only [Sum.inl.injEq, false_and, or_false] at h₂
    rcases h₂ with ⟨rfl,h₂,rfl,rfl,rfl⟩
    cases h₂.trans h₃
    exact ⟨rfl, .inl ⟨_,hrbi,rfl⟩⟩
  · rcases h₂ with (⟨rfl,-⟩|⟨rfl,rfl,rfl⟩)
    · simp at h₁
    · exact ⟨rfl, .inr rfl⟩

aegis_spec "core::starknet::info::get_contract_address" :=
  fun m _ s _ s' ρ =>
  s = s' ∧ (ρ = .inl m.contractAddress ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_contract_address" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_contract_address»
  rintro ⟨_,_,_,_,_,_,_,_,_,_,rfl,(⟨_,_,_,rfl,h₃,_,_⟩|h₁),h₂⟩
  · simp only [Sum.inl.injEq, false_and, or_false] at h₂
    rcases h₂ with ⟨rfl,h₂,rfl,rfl,rfl⟩
    cases h₂.trans h₃
    exact ⟨rfl, .inl rfl⟩
  · rcases h₂ with (⟨rfl,-⟩|⟨rfl,rfl,rfl⟩)
    · simp at h₁
    · exact ⟨rfl, .inr rfl⟩

aegis_spec "core::starknet::info::get_block_timestamp" :=
  fun m _ s _ s' ρ =>
  s = s' ∧ (ρ = .inl m.blockTimestamp ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_block_timestamp" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_block_timestamp»
  rintro ⟨_,_,_,_,_,_,_,_,rfl,(⟨rbi,h₁,rfl⟩|h₁),h₂⟩
  · simp only [Sum.inl.injEq, false_and, or_false] at h₂
    rcases h₂ with ⟨rfl,h₂,rfl,rfl,rfl⟩
    cases h₂.trans h₁
    exact ⟨rfl, .inl rfl⟩
  · rcases h₂ with (⟨rfl,-⟩|⟨rfl,rfl,rfl⟩)
    · simp at h₁
    · exact ⟨rfl, .inr rfl⟩
