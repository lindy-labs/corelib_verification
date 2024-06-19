import CorelibVerification.Load
import CorelibVerification.Aux.Result
import CorelibVerification.Aux.PanicResult

namespace Sierra

aegis_spec "core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u16>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u16>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u32>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop

aegis_spec "core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) =>
  a.succeeds ∧ ρ.succeeds ∧ a.get! = ρ.get!
  ∨ a.fails ∧ ρ.fails

aegis_prove "core::starknet::SyscallResultTraitImpl<core::integer::u64>::unwrap_syscall" :=
  fun _ (a : Result _) (ρ : PanicResult _) => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; aesop
  · right; aesop
