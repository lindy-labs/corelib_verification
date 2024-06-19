import CorelibVerification.Corelib.Starknet.SyscallResult
import CorelibVerification.Corelib.Integer

namespace Sierra

aegis_spec "core::starknet::info::get_execution_info" :=
  fun m _ s _ s' (ρ : PanicResult _) =>
  s = s' ∧
  ((∃ rei rbi rti, ρ = .inl rei ∧
      m.boxHeap .ExecutionInfo rei = .some ⟨rbi, rti,
      m.callerAddress, m.contractAddress, m.entryPointSelector⟩
      ∧ m.boxHeap .BlockInfo rbi = .some ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩
      ∧ m.boxHeap .TxInfo rti = .some ⟨m.txVersion, m.txContract, m.txMaxFee, m.txSignature,
        m.txHash, m.txChainIdentifier, m.txNonce⟩)
    ∨ ρ.fails)

aegis_prove "core::starknet::info::get_execution_info" :=
  fun m _ s _ s' (ρ : PanicResult _) => by
  unfold «spec_core::starknet::info::get_execution_info»
  rintro ⟨_,_,_,_,_,(⟨⟨_,_,_,_,_,h₁,h₃,h₄,rfl,rfl,rfl⟩,h₂,h₅⟩|⟨h₁,h₂⟩)⟩
  · rcases h₅ with (⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · simp only [sizeOf_nat, Nat.lt_eq, SierraType.Box.sizeOf_spec,
        SierraType.ContractAddress.sizeOf_spec, Result.succeeds_inl, PanicResult.succeeds_inl,
        Result.get!_inl, PanicResult.get!_inl, true_and, Result.fails_inl, PanicResult.fails_inl,
        and_self, or_false, SierraType.U64.sizeOf_spec, SierraType.Felt252.sizeOf_spec,
        SierraType.U128.sizeOf_spec] at h₁ h₂ h₃ h₄
      subst h₂
      exact ⟨rfl, .inl ⟨_, _, _, rfl, h₁, h₃, h₄⟩⟩
    · exact ⟨rfl, .inr rfl⟩
  · simp only [Result.succeeds_inr, Result.get!_inr, false_and, Result.fails_inr, true_and,
      false_or] at h₁
    rcases h₂ with (⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · simp at h₁
    · exact ⟨rfl, .inr rfl⟩

aegis_spec "core::starknet::info::get_caller_address" :=
  fun m _ s _ s' (ρ : PanicResult _) =>
  s = s' ∧ (ρ = .inl m.callerAddress ∨ ρ.fails)

aegis_prove "core::starknet::info::get_caller_address" :=
  fun m _ s _ s' (ρ : PanicResult _) => by
  unfold «spec_core::starknet::info::get_caller_address»
  rintro ⟨_,_,_,_,_,_,_,_,_,_,rfl,h,(⟨rfl,h',rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩
  · simp only [PanicResult.fails_inl, or_false] at h
    rcases h with ⟨rei,_,_,h₁,h₂,-,-⟩
    cases h₁
    cases h'.trans h₂
    exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inr rfl⟩

aegis_spec "core::starknet::info::get_block_info" :=
  fun m _ s _ s' (ρ : PanicResult _) =>
  s = s' ∧
  ((∃ rbi,
      m.boxHeap .BlockInfo rbi = .some ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩
      ∧ ρ = .inl rbi)
    ∨ ρ.fails)

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
  fun m _ s _ s' (ρ : PanicResult _) =>
  s = s' ∧ (ρ = .inl m.contractAddress ∨ ρ.fails)

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
  fun m _ s _ s' (ρ : PanicResult _) =>
  s = s' ∧ (ρ = .inl m.blockTimestamp ∨ ρ.fails)

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
