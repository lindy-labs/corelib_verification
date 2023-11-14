import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.Starknet.ContractAddress
import CorelibVerification.Aux.Bool
import CorelibVerification.Load

namespace Sierra

aegis_spec "core::starknet::storage_access::StorageAccessU8::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U8_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U8_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StorageAccessU8::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StorageAccessU8::read»
  sierra_simp'
  aesop

aegis_spec "core::starknet::storage_access::StorageAccessU32::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U32_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U32_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StorageAccessU32::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StorageAccessU32::read»
  sierra_simp'
  aesop

aegis_spec "core::starknet::storage_access::StorageAccessU64::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U64_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U64_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StorageAccessU64::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StorageAccessU64::read»
  sierra_simp'
  aesop

aegis_spec "core::starknet::storage_access::StorageAccessU128::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < U128_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ U128_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StorageAccessU128::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StorageAccessU128::read»
  sierra_simp'
  aesop

aegis_spec "core::starknet::storage_access::StorageAccessContractAddress::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r := (sys.contracts m.contractAddress).storage b_add.cast
  ρ_sys = sys
  ∧ (r.val < CONTRACT_ADDRESS_MOD ∧ ρ = .inl (.inl r.cast)
    ∨ CONTRACT_ADDRESS_MOD ≤ r.val ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StorageAccessContractAddress::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StorageAccessContractAddress::read»
  sierra_simp'
  aesop

aegis_spec "core::starknet::storage_access::StorageAccessU256::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ =>
  let r₁ := (sys.contracts m.contractAddress).storage b_add.cast
  let r₂ := (sys.contracts m.contractAddress).storage (b_add.cast + 1)
  ρ_sys = sys
  ∧ (r₁.val < U128_MOD ∧ r₂.val < U128_MOD ∧ ρ = .inl (.inl (r₁.cast, r₂.cast))
    ∨ (U128_MOD ≤ r₁.val ∨ U128_MOD ≤ r₂.val) ∧ ρ.isRight
    ∨ ∃ e, ρ = .inl (.inr e))

aegis_prove "core::starknet::storage_access::StorageAccessU256::read" :=
  fun m _ _ sys _ b_add _ _ ρ_sys ρ => by
  unfold «spec_core::starknet::storage_access::StorageAccessU256::read»
  sierra_simp'
  rename_i x x_1 x_2 x_3 x_4
  intro h_auto
  simp_all only [Int.cast_one, Nat.cast_ofNat, Int.int_cast_ofNat, List.nil_append, exists_and_right, Sum.exists,
    Sum.inl.injEq, and_false, or_false, exists_eq_left, exists_false, false_and, and_true, false_or, exists_const,
    true_and, exists_and_left, Sum.inr.injEq, Sum.isRight_inl, exists_eq', or_true, Sum.isRight_inr, or_self]
  unhygienic aesop_cases h_auto <;> [(unhygienic aesop_cases h), skip]
  · unhygienic with_reducible aesop_destruct_products
    aesop_subst right_1
    simp_all only [true_and]
    unhygienic aesop_cases right <;> [(unhygienic aesop_cases h), skip]
    · unhygienic with_reducible aesop_destruct_products
      aesop_subst [left, right_1, right_2]
      simp_all only [Sum.inl.injEq, Prod.mk.injEq, true_and, Sum.isRight_inl, and_false, exists_false, or_self,
        or_false]
      apply And.intro
      · exact left_2
      · apply Eq.refl
    · simp_all only [true_and]
      unhygienic with_reducible aesop_destruct_products
      aesop_subst [right_1, left_2]
      simp_all only [and_false, and_true, exists_false, or_false, false_or]
      apply Or.inr
      exact left
    · simp_all only [true_and]
      unhygienic with_reducible aesop_destruct_products
      aesop_subst [h, left]
      simp_all only [Sum.inl.injEq, and_false, Sum.isRight_inl, Sum.inr.injEq, exists_eq', or_true]
  · simp_all only [true_and]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [left, h]
    simp_all only [Sum.inl.injEq, and_false, Sum.isRight_inl, Sum.inr.injEq, exists_eq', or_true]
  · simp_all only [true_and]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [left_1, h]
    simp_all only [and_false, true_or, Sum.isRight_inr, and_self, exists_false, or_false, or_true]

aegis_spec "core::starknet::storage_access::StorageAccessBool::read" :=
  fun m _ s _ b_addr _ s' ρ =>
  let r := (s.contracts m.contractAddress).storage (b_addr : StorageAddress)
  s' = s
  ∧ (ρ = .inl (Bool.toSierraBool (r ≠ 0)) ∨ ρ.isRight)

aegis_prove "core::starknet::storage_access::StorageAccessBool::read" :=
  fun m _ s _ b_addr _ s' ρ => by
  unfold «spec_core::starknet::storage_access::StorageAccessBool::read»
  simp only [StorageAddress, ADDRESS_MOD]
  aesop
