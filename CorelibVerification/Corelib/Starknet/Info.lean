import CorelibVerification.Corelib.Starknet.SyscallResult
import CorelibVerification.Corelib.Integer

namespace Sierra

aegis_spec "core::starknet::info::get_execution_info" :=
  fun m _ s _ s' ρ =>
  s = s' ∧
  ((∃ rei rbi rti, ρ = .inl rei ∧
      m.boxHeap .V2ExecutionInfo rei = .some ⟨rbi, rti,
      m.callerAddress, m.contractAddress, m.entryPointSelector⟩
      ∧ m.boxHeap .BlockInfo rbi = .some ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩
      ∧ m.boxHeap .V2TxInfo rti = .some ⟨m.txVersion, m.txContract, m.txMaxFee, m.txSignature,
        m.txHash, m.txChainIdentifier, m.txNonce, m.txResourceBounds, m.txTip, m.txPaymasterData,
        m.txDataAvailabilityNonce, m.txDataAvailabilityFee, m.txAccountDeploymentData⟩)
    ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_execution_info" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_execution_info»
  rintro ⟨_,_,ρ',h⟩
  rcases h with (⟨h₁,h,rfl,rfl⟩|⟨h,rfl,rfl⟩)
  · rcases h with (h|h)
    · simp only [Sum.isLeft_inl, Sum.getLeft?_inl, Option.get!_some, true_and] at h
      rcases h with ⟨h,rfl⟩
      rcases h₁ with ⟨_,rbi,_,rti,_,h₁,h₂,h₃,rfl,rfl,rfl⟩
      refine ⟨rfl, .inl ?_⟩
      use ρ'.getLeft?.get!
      use rbi
      use rti
      refine ⟨?_, h₁, h₂, h₃⟩
      rcases ρ'  -- TODO
      · simp
      · simp at h
    · simp at h
  · simp only [Sum.isLeft_inr, Bool.false_eq_true, Sum.getLeft?_inr, Option.get!_none,
      Nat.default_eq_zero, false_and, Sum.isRight_inr, true_and, false_or] at h
    refine ⟨rfl, .inr ?_⟩
    assumption

aegis_spec "core::starknet::info::get_caller_address" :=
  fun m _ s _ s' ρ =>
  s = s' ∧ (ρ = .inl m.callerAddress ∨ ρ.isRight)

aegis_prove "core::starknet::info::get_caller_address" :=
  fun m _ s _ s' ρ => by
  unfold «spec_core::starknet::info::get_caller_address»
  rintro ⟨_,_,_,_,_,_,_,_,_,_,rfl,h,(⟨rfl,h',rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, SierraType.Box.sizeOf_spec, Sum.inl.injEq,
      SierraType.ContractAddress.sizeOf_spec, SierraType.U64.sizeOf_spec,
      SierraType.Felt252.sizeOf_spec, SierraType.U128.sizeOf_spec, SierraType.U32.sizeOf_spec,
      exists_and_left, exists_eq_left', Sum.isRight_inl, Bool.false_eq_true, or_false] at h
    obtain ⟨rei,_,h⟩ := h
    sorry
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
    cases h₂.symm.trans h₃
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
    cases h₂.symm.trans h₃
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
    cases h₂.symm.trans h₁
    exact ⟨rfl, .inl rfl⟩
  · rcases h₂ with (⟨rfl,-⟩|⟨rfl,rfl,rfl⟩)
    · simp at h₁
    · exact ⟨rfl, .inr rfl⟩
