import CorelibVerification.Load

namespace Sierra

aegis_load_file "full.sierra"

aegis_spec "core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq', exists_const]
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall»
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall»
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall»
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall»
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall»
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall" :=
  fun _ a ρ => by
  unfold «spec_core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall»
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]
