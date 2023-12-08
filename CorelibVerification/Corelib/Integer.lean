import CorelibVerification.Aux.ZMod
import CorelibVerification.Corelib.Result
import CorelibVerification.Aux.UInt256
import CorelibVerification.Aux.Bool
import Aegis.Tactic

syntax "sierra_simp'" : tactic
macro_rules
| `(tactic|sierra_simp') =>
  `(tactic|
    simp only [Prod.mk.inj_iff, and_assoc, Bool.coe_toSierraBool, Bool.toSierraBool_coe,
      exists_and_left, exists_and_right, exists_eq_left, exists_eq_right, exists_eq_right',
      exists_eq_left', not, or, and,
      SierraBool_toBool_inl, SierraBool_toBool_inr, Bool.toSierraBool_true, Bool.toSierraBool_false,
      Int.ofNat_eq_coe, Nat.cast_one, Nat.cast_zero, Int.cast_zero, ZMod.val_zero,
      exists_or, exists_const, ← or_and_right, ne_or_eq, true_and, false_and, eq_or_ne, and_true,
      le_or_gt, lt_or_ge, lt_or_le, le_or_lt, and_false, false_or, or_false,
      Bool.toSierraBool_decide_inl', Bool.toSierraBool_decide_inr',
      not_ne_iff, Nat.not_lt];
    try simp only [← exists_and_left, ← exists_and_right, ← exists_or])

open Sierra Classical

aegis_spec "core::integer::U128MulGuaranteeDestruct::destruct" :=
  fun _ _ _ _ _ =>
  True

aegis_prove "core::integer::U128MulGuaranteeDestruct::destruct" :=
   fun _ _ _ _ _ _ => True.intro

aegis_spec "core::result::ResultTraitImpl<core::integer::u8, core::integer::u8>::expect<core::integer::u8Drop>" :=
  fun _ a b ρ =>
  ρ = Sum.map id (fun _ => ((), [b])) a

aegis_prove "core::result::ResultTraitImpl<core::integer::u8, core::integer::u8>::expect<core::integer::u8Drop>" :=
  fun _ a b ρ => by
  unfold «spec_core::result::ResultTraitImpl<core::integer::u8, core::integer::u8>::expect<core::integer::u8Drop>»
  rintro ⟨_, _, _, _, (⟨rfl, rfl⟩|⟨h⟩)⟩
  · aesop
  · aesop

aegis_spec "core::integer::U8Sub::sub" :=
  fun _ _ a b _ ρ =>
  (b.val ≤ a.val ∧ ρ = .inl (a - b)) ∨ (a.val < b.val ∧ ρ.isRight )

aegis_prove "core::integer::U8Sub::sub" := fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U8Sub::sub»
  aesop

instance U128_MOD_lt_PRIME : Fact (U128_MOD < PRIME) := ⟨by norm_num [U128_MOD, PRIME]⟩

instance : NeZero U128_MOD := ⟨by norm_num [U128_MOD]⟩

aegis_spec "core::integer::u128_wide_mul" :=
  fun _ _ a b _ ρ =>
  ρ = (a.hmul b, a * b)

aegis_prove "core::integer::u128_wide_mul" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::u128_checked_mul" :=
  fun _ _ a b  _ ρ =>
  (a.val * b.val < U128_MOD ∧ ρ = .inl (a * b)) ∨ (U128_MOD ≤ a.val * b.val ∧ ρ = .inr ())

aegis_prove "core::integer::u128_checked_mul" :=
  fun _ _ a b  _ ρ => by
  unfold «spec_core::integer::u128_checked_mul»
  simp only [Prod.mk.injEq, ne_eq, forall_exists_index, and_imp,
    forall_eq_apply_imp_iff', forall_eq]
  rintro _ _ rfl rfl (⟨h,rfl⟩|⟨h,rfl⟩)
  · rw [← ZMod.cast_zero (n := U128_MOD),
      (ZMod.cast_injective_of_lt U128_MOD_lt_PRIME.out).eq_iff, ZMod.hmul_eq_zero_iff] at h
    simp_all only [and_self, and_false, or_false]
  · rw [← @ne_eq, ← ZMod.cast_zero (n := U128_MOD),
      (ZMod.cast_injective_of_lt U128_MOD_lt_PRIME.out).ne_iff] at h
    simp_all [ZMod.hmul_eq_zero_iff]

aegis_spec "core::option::OptionTraitImpl<core::integer::u128>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u128>::expect" :=
  fun _ a b ρ => by
  unfold «spec_core::option::OptionTraitImpl<core::integer::u128>::expect»
  aesop

aegis_spec "core::integer::U128Mul::mul" :=
  fun _ _ a b _ ρ =>
  (a.val * b.val < U128_MOD ∧ ρ = .inl (a * b)) ∨ (U128_MOD ≤ a.val * b.val ∧ ρ.isRight)

aegis_prove "core::integer::U128Mul::mul" := fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U128Mul::mul»
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::integer::u128Drop>" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::integer::u128Drop>" :=
  fun _ a err ρ => by
  unfold «spec_core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::integer::u128Drop>»
  aesop

aegis_spec "core::integer::U128Sub::sub" := fun _ _ a b _ ρ =>
  if b.val ≤ a.val then ρ = .inl (a - b) else ρ.isRight

aegis_prove "core::integer::U128Sub::sub" := fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U128Sub::sub»
  aesop (add forward safe Nat.lt_le_asymm)

aegis_spec "core::integer::u128_try_from_felt252" := fun _ _ a _ ρ =>
  a.val < U128_MOD ∧ ρ = .inl a.cast ∨ U128_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "core::integer::u128_try_from_felt252" := fun _ _ a _ ρ => by
  unfold «spec_core::integer::u128_try_from_felt252»
  rintro ⟨b,c,(⟨h,rfl⟩|⟨hne,h,rfl⟩)⟩
  · aesop
  · have : 2 ^ 128 ≤ a.val := by
      rw [← ZMod.val_ne_zero, ← pos_iff_ne_zero] at hne
      rw [← h]
      exact le_trans (Nat.le_mul_of_pos_right hne) (Nat.le_add_right _ c.val)
    right; exact ⟨this, rfl⟩

aegis_spec "core::integer::U128BitNot::bitnot" := fun _ _ a _ ρ =>
  ρ = .inl (340282366920938463463374607431768211455 - a)

aegis_prove "core::integer::U128BitNot::bitnot" := fun _ _ a _ ρ => by
  unfold «spec_core::integer::U128BitNot::bitnot»
  have hlt' : 340282366920938463463374607431768211455 < U128_MOD := by norm_num [U128_MOD]
  rintro ⟨_, _, _, h, (⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
    <;> split_ifs at h with hlt
    <;> erw [ZMod.val_cast_of_lt hlt'] at hlt
  · aesop
  · aesop
  · exfalso
    exact Nat.lt_le_asymm a.val_lt (lt_of_not_le hlt)

aegis_spec "core::integer::u64_try_as_non_zero" :=
  fun _ a ρ =>
  (a = 0 ∧ ρ = .inr ()) ∨ (a ≠ 0 ∧ ρ = .inl a)

aegis_prove "core::integer::u64_try_as_non_zero" :=
  fun _ a ρ => by
  unfold «spec_core::integer::u64_try_as_non_zero»
  aesop

aegis_spec "core::integer::u128_try_as_non_zero" :=
  fun _ a ρ =>
  (a = 0 ∧ ρ = .inr ()) ∨ (a ≠ 0 ∧ ρ = .inl a)

aegis_prove "core::integer::u128_try_as_non_zero" :=
  fun _ a ρ => by
  unfold «spec_core::integer::u128_try_as_non_zero»
  aesop

aegis_spec "core::integer::u256_try_as_non_zero" :=
  fun _ a ρ =>
  (a = (0, 0) ∧ ρ = .inr ()) ∨ (((a.1 ≠ 0) ∨ (a.2 ≠ 0)) ∧ ρ = .inl a)

aegis_prove "core::integer::u256_try_as_non_zero" :=
  fun _ a ρ => by
  unfold «spec_core::integer::u256_try_as_non_zero»
  aesop

aegis_spec "core::integer::u64_as_non_zero" :=
  fun _ a ρ =>
  (a ≠ 0 ∧ ρ = .inl a) ∨ (a = 0 ∧ ρ.isRight)

aegis_prove "core::integer::u64_as_non_zero" :=
  fun _ a ρ => by
  unfold «spec_core::integer::u64_as_non_zero»
  aesop

aegis_spec "core::integer::u128_as_non_zero" :=
  fun _ a ρ =>
  (a ≠ 0 ∧ ρ = .inl a) ∨ (a = 0 ∧ ρ.isRight)

aegis_prove "core::integer::u128_as_non_zero" :=
  fun _ a ρ => by
  unfold «spec_core::integer::u128_as_non_zero»
  aesop

aegis_spec "core::integer::u256_as_non_zero" :=
  fun _ a ρ =>
  ((a.1 ≠ 0 ∨ a.2 ≠ 0) ∧ ρ = .inl a) ∨ (a = (0, 0) ∧ ρ.isRight)

aegis_prove "core::integer::u256_as_non_zero" :=
  fun _ a ρ => by
  unfold «spec_core::integer::u256_as_non_zero»
  rintro ⟨_,_,_,(⟨rfl,rfl⟩|h),h'⟩
  · aesop
  · rcases h' with (⟨rfl,rfl⟩|h') <;> aesop

aegis_spec "core::integer::u256_from_felt252" :=
  fun _ _ a _ ρ =>
  U128_MOD * ρ.2.val + ρ.1.val = a.val

aegis_prove "core::integer::u256_from_felt252" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::integer::u256_from_felt252»
  rintro ⟨_,_,(⟨h,rfl⟩|⟨_,_,rfl⟩)⟩ <;> aesop (add forward safe ZMod.val_cast_eq_val_of_lt)

aegis_spec "core::integer::U64TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  (a ≠ 0 ∧ ρ = .inl (.inl a)) ∨ (a = 0 ∧ ρ.isRight)

aegis_prove "core::integer::U64TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold «spec_core::integer::U64TryIntoNonZero::try_into»
  aesop

aegis_spec "core::integer::U128TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  (a ≠ 0 ∧ ρ = .inl (.inl a)) ∨ (a = 0 ∧ ρ.isRight)

aegis_prove "core::integer::U128TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold «spec_core::integer::U128TryIntoNonZero::try_into»
  aesop

aegis_spec "core::integer::U256TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  ((a.1 ≠ 0 ∨ a.2 ≠ 0) ∧ ρ = .inl (.inl a)) ∨ (a.1 = 0 ∧ a.2 = 0 ∧ ρ.isRight)

aegis_prove "core::integer::U256TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold «spec_core::integer::U256TryIntoNonZero::try_into»
  rintro ⟨_,_,_,(⟨h,rfl⟩|h),h'⟩
  · rcases h' with (⟨h',rfl⟩|h') <;> aesop
  · aesop

aegis_spec "core::integer::Felt252TryIntoU8::try_into" :=
  fun _ _ a _ ρ =>
  (a.val < U8_MOD ∧ ρ = .inl a.cast) ∨ (U8_MOD ≤ a.val ∧ ρ.isRight)

aegis_prove "core::integer::Felt252TryIntoU8::try_into" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::integer::Felt252TryIntoU8::try_into»
  aesop

aegis_spec "core::integer::Felt252TryIntoU32::try_into" :=
  fun _ _ a _ ρ =>
  (a.val < U32_MOD ∧ ρ = .inl a.cast) ∨ (U32_MOD ≤ a.val ∧ ρ.isRight)

aegis_prove "core::integer::Felt252TryIntoU32::try_into" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::integer::Felt252TryIntoU32::try_into»
  aesop

aegis_spec "core::integer::Felt252TryIntoU64::try_into" :=
  fun _ _ a _ ρ =>
  (a.val < U64_MOD ∧ ρ = .inl a.cast) ∨ (U64_MOD ≤ a.val ∧ ρ.isRight)

aegis_prove "core::integer::Felt252TryIntoU64::try_into" :=
  fun _ _ a _ ρ => by
  unfold «spec_core::integer::Felt252TryIntoU64::try_into»
  aesop

aegis_spec "core::integer::U32Add::add" :=
  fun _ _ a b _ ρ =>
  (a.val + b.val < U32_MOD ∧ ρ = .inl (a + b)) ∨ (U32_MOD ≤ a.val + b.val ∧ ρ.isRight)

aegis_prove "core::integer::U32Add::add" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U32Add::add»
  aesop

aegis_spec "core::integer::U32Sub::sub" :=
  fun _ _ a b _ ρ =>
  (b.val ≤ a.val ∧ ρ = .inl (a - b)) ∨ (a.val < b.val ∧ ρ.isRight)

aegis_prove "core::integer::U32Sub::sub" :=
   fun _ _ a b _ ρ => by
   unfold «spec_core::integer::U32Sub::sub»
   aesop

aegis_spec "core::integer::U64Add::add" :=
  fun _ _ a b _ ρ =>
  (a.val + b.val < U64_MOD ∧ ρ = .inl (a + b)) ∨ (U64_MOD ≤ a.val + b.val ∧ ρ.isRight)

aegis_prove "core::integer::U64Add::add" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U64Add::add»
  aesop

aegis_spec "core::integer::U64Sub::sub" :=
  fun _ _ a b _ ρ =>
  (b.val ≤ a.val ∧ ρ = .inl (a - b)) ∨ (a.val < b.val ∧ ρ.isRight)

aegis_prove "core::integer::U64Sub::sub" :=
   fun _ _ a b _ ρ => by
   unfold «spec_core::integer::U64Sub::sub»
   aesop

aegis_spec "core::option::OptionTraitImpl<core::integer::u64>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u64>::expect" :=
  fun _ a b ρ => by
  unfold «spec_core::option::OptionTraitImpl<core::integer::u64>::expect»
  aesop

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u64>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u64>>::expect" :=
  fun _ a err ρ => by
  unfold «spec_core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u64>>::expect»
  aesop

aegis_spec "core::integer::U64Div::div" :=
  fun _ _ a b _ ρ =>
  (b ≠ 0 ∧ ∃ ρ', ρ = .inl ρ' ∧ ρ'.val = a.val / b.val) ∨ (b = 0 ∧ ρ.isRight)

aegis_prove "core::integer::U64Div::div" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U64Div::div»
  aesop (add norm simp Nat.mul_add_div_eq_of_lt)

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u128>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u128>>::expect" :=
  fun _ a err ρ => by
  unfold «spec_core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u128>>::expect»
  aesop

aegis_spec "core::integer::U128Div::div" :=
  fun _ _ a b _ ρ =>
  (b ≠ 0 ∧ ∃ ρ', ρ = .inl ρ' ∧ ρ'.val = a.val / b.val) ∨ (b = 0 ∧ ρ.isRight)

aegis_prove "core::integer::U128Div::div" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U128Div::div»
  aesop (add norm simp Nat.mul_add_div_eq_of_lt)

aegis_spec "core::integer::U128Add::add" :=
  fun _ _ a b _ ρ =>
  (a.val + b.val < U128_MOD ∧ ρ = .inl (a + b)) ∨ (U128_MOD ≤ a.val + b.val ∧ ρ.isRight)

aegis_prove "core::integer::U128Add::add" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U128Add::add»
  aesop

aegis_spec "core::integer::u256_overflowing_add" :=
  fun _ _ (a b : UInt256) _ ρ =>
  ρ = (a + b, Bool.toSierraBool (U256_MOD ≤ a.val + b.val))

aegis_prove "core::integer::u256_overflowing_add" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::u256_overflowing_add»
  rintro ⟨aₗ,aₕ,bₗ,bₕ,_,_,rfl,rfl,(⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩)⟩
    <;> injection h₂ with h₂₁ h₂₂
    <;> rcases h₂₁ with rfl
    <;> rcases h₂₂ with rfl
  -- Case: high value addition does not overflow
  · rcases h₃ with (⟨h₃,rfl⟩|⟨h₃,(⟨h₄,rfl⟩|⟨h₄,rfl⟩)⟩)
    -- Case: low value addition does not overflow
    · simp only [h₃, ite_true, add_zero, Prod.mk.injEq, true_and, Bool.toSierraBool]
      have : ¬ U256_MOD ≤ UInt256.val (aₗ, aₕ) + UInt256.val (bₗ, bₕ) := by
        rw [UInt256.val_add_val_lt_iff, not_or, not_le, not_and_or, not_le, not_le]
        simp_all
      simp [this, UInt256.add_def, h₃]
    -- Case: low value addition overflows, carry does not
    · rw [ZMod.val_add_of_lt h₁] at h₄
      rw [UInt256.add_def]
      rw [← not_lt] at h₃
      have : ¬ U256_MOD ≤ UInt256.val (aₗ, aₕ) + UInt256.val (bₗ, bₕ) := by
        simp only [not_or, not_le, not_and, UInt256.val_add_val_lt_iff]
        refine ⟨h₁, fun _ => ?_⟩
        rwa [Int.ofNat_eq_coe, Nat.cast_one, Int.cast_one, ZMod.val_one] at h₄
      simp [this, h₃]
    -- Case: low value addition and carry overlow
    · rw [← not_lt] at h₃
      have : U256_MOD ≤ UInt256.val (aₗ, aₕ) + UInt256.val (bₗ, bₕ) := by
        rw [UInt256.val_add_val_lt_iff]; right
        refine ⟨le_of_not_lt h₃, ?_⟩
        simp_all [ZMod.val_one, ZMod.val_add_of_lt h₁, h₄]
      simp [this, UInt256.add_def, h₃]
  -- Case: high value addition overflows
  · have : U256_MOD ≤ UInt256.val (aₗ, aₕ) + UInt256.val (bₗ, bₕ) := by
      rw [UInt256.val_add_val_lt_iff]; left; exact h₁
    simp [this]
    rcases h₃ with (⟨h₃,rfl⟩|⟨h₃,(⟨_,rfl⟩|⟨_,rfl⟩)⟩)
    · simp [Prod.mk.injEq, and_true, UInt256.add_def, true_and, h₃]
    · simp [UInt256.add_def, not_lt_of_le h₃]
    · simp [UInt256.add_def, not_lt_of_le h₃]

aegis_spec "core::integer::u256_checked_add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) =>
  (a.val + b.val < U256_MOD ∧ ρ = .inl (a + b))
  ∨ (U256_MOD ≤ a.val + b.val ∧ ρ = .inr ())

aegis_prove "core::integer::u256_checked_add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) => by
  unfold «spec_core::integer::u256_checked_add»
  rintro ⟨_,_,_,_,he,(⟨h,rfl⟩|h)⟩
  · aesop
  · aesop

aegis_spec "core::option::OptionTraitImpl<core::integer::u256>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u256>::expect" :=
  fun _ a err ρ => by
  unfold «spec_core::option::OptionTraitImpl<core::integer::u256>::expect»
  aesop

aegis_spec "core::integer::U256Add::add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  (a.val + b.val < U256_MOD ∧ ρ = .inl (a + b))
  ∨ (U256_MOD ≤ a.val + b.val ∧ ρ.isRight)

aegis_prove "core::integer::U256Add::add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold «spec_core::integer::U256Add::add»
  rintro ⟨_,_,_,_,he,(⟨h,rfl⟩|h)⟩
  · aesop
  · aesop

aegis_spec "core::integer::u256_overflow_sub" :=
  fun _ _ (a b : UInt256) _ ρ =>
  ρ = (a - b, Bool.toSierraBool (a.val < b.val))

aegis_prove "core::integer::u256_overflow_sub" :=
  fun _ _ (a b : UInt256) _ ρ => by
  unfold «spec_core::integer::u256_overflow_sub»
  rintro ⟨aₗ,aₕ,bₗ,bₕ,_,_,rfl,rfl,(⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩)⟩
  <;> rcases h₃ with (⟨h₃,rfl⟩|⟨h₃,(⟨h₄,rfl⟩|⟨h₄,rfl⟩)⟩)
  <;> injection h₂ with h₂ h₂'
  <;> cases h₂ <;> cases h₂'
  <;> simp only [UInt256.sub_def]
  <;> try rw [← not_lt] at h₃
  · have : ¬ U128_MOD * ZMod.val aₕ + ZMod.val aₗ < U128_MOD * ZMod.val bₕ + ZMod.val bₗ := by
      intro h
      rcases (UInt256.val_lt_val_iff ⟨aₗ, aₕ⟩ ⟨bₗ, bₕ⟩).mp h with (h|⟨h',-⟩)
      · apply Nat.le_lt_asymm h₁ h
      · exact h₃ h'
    simp [UInt256.val, h₃, this]
  · have : ¬ U128_MOD * ZMod.val aₕ + ZMod.val aₗ < U128_MOD * ZMod.val bₕ + ZMod.val bₗ := by
      intro h
      rw [ZMod.val_sub h₁, Int.ofNat_eq_coe, Nat.cast_one, Int.cast_one, ZMod.val_one] at h₄
      rcases (UInt256.val_lt_val_iff ⟨aₗ, aₕ⟩ ⟨bₗ, bₕ⟩).mp h with (h|⟨-,h⟩)
      · apply Nat.le_lt_asymm h₁ h
      · simp_all only [ge_iff_le, le_refl, tsub_eq_zero_of_le, nonpos_iff_eq_zero]
    simp [UInt256.val, h₃, this]
  · have : U128_MOD * ZMod.val aₕ + ZMod.val aₗ < U128_MOD * ZMod.val bₕ + ZMod.val bₗ := by
      rw [ZMod.val_sub h₁, Int.ofNat_eq_coe, Nat.cast_one, Int.cast_one, ZMod.val_one] at h₄
      apply (UInt256.val_lt_val_iff ⟨aₗ, aₕ⟩ ⟨bₗ, bₕ⟩).mpr; right; constructor
      · assumption
      · simp only [ge_iff_le, Nat.lt_one_iff, tsub_eq_zero_iff_le] at h₄
        apply Nat.le_antisymm h₄ h₁
    simp [UInt256.val, h₃, this]
  all_goals
    have : U128_MOD * ZMod.val aₕ + ZMod.val aₗ < U128_MOD * ZMod.val bₕ + ZMod.val bₗ := by
      apply (UInt256.val_lt_val_iff ⟨aₗ, aₕ⟩ ⟨bₗ, bₕ⟩).mpr; left; assumption
    simp [UInt256.val, h₃, this]

aegis_spec "core::integer::u256_checked_sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) =>
  (b.val ≤ a.val ∧ ρ = .inl (a - b))
  ∨ (a.val < b.val ∧ ρ = .inr ())

aegis_prove "core::integer::u256_checked_sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) => by
  unfold «spec_core::integer::u256_checked_sub»
  rintro ⟨_,_,_,_,he,(⟨h,rfl⟩|h)⟩
  · aesop
  · aesop

aegis_spec "core::integer::U256Sub::sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  (b.val ≤ a.val ∧ ρ = .inl (a - b))
  ∨ (a.val < b.val ∧ ρ.isRight)

aegis_prove "core::integer::U256Sub::sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold «spec_core::integer::U256Sub::sub»
  rintro ⟨_,_,_,_,he,(⟨h,rfl⟩|h)⟩
  · aesop
  · aesop

aegis_spec "core::integer::u256_overflow_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 × _) =>
  ρ = (a * b, Bool.toSierraBool (U256_MOD ≤ a.val * b.val))

aegis_spec "core::integer::U128PartialEq::eq" :=
  fun _ a b ρ =>
  ρ = (Bool.toSierraBool (a = b))

aegis_prove "core::integer::U128PartialEq::eq" :=
  fun _ a b ρ => by
  unfold «spec_core::integer::U128PartialEq::eq»
  aesop

aegis_spec "core::integer::U128PartialEq::ne" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a ≠ b)

aegis_prove "core::integer::U128PartialEq::ne" :=
  fun _ a b ρ => by
  unfold «spec_core::integer::U128PartialEq::ne»
  rintro rfl
  simp_all

aegis_spec "core::integer::U128PartialOrd::gt" :=
  fun _ _ a b _ ρ =>
  ρ = Bool.toSierraBool (b.val < a.val)

aegis_prove "core::integer::U128PartialOrd::gt" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U128PartialOrd::gt»
  aesop

aegis_spec "core::integer::U128PartialOrd::lt" :=
  fun _ _ a b _ ρ =>
  ρ = Bool.toSierraBool (a.val < b.val)

aegis_prove "core::integer::U128PartialOrd::lt" :=
  fun _ _ a b _ ρ => by
  unfold «spec_core::integer::U128PartialOrd::lt»
  aesop

theorem U128_MOD_mul_U128_MOD : U128_MOD * U128_MOD = U256_MOD := rfl

theorem U128_MOD_pos : 0 < U128_MOD := by norm_num [U128_MOD]



aegis_prove "core::integer::u256_overflow_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 × _) => by
  rcases a with ⟨aₗ, aₕ⟩
  rcases b with ⟨bₗ, bₕ⟩
  unfold «spec_core::integer::u256_overflow_mul»
  sierra_simp'
  rintro (⟨h,h₁⟩|⟨h,rfl⟩)
  · rcases h₁ with (⟨h₁,h₂⟩|⟨h₁,rfl⟩)
    · rcases h₂ with (⟨h₂,h₃⟩|⟨h₂,rfl⟩)
      · rcases h₃ with (⟨h₃,h₄⟩|⟨h₃,h₄⟩)
        · rcases h₄ with (⟨h₄,rfl⟩|⟨h₄,rfl⟩)
          · simp only [UInt256.mul_def, Prod.mk.injEq, Bool.toSierraBool_decide_inl', not_le, true_and]
            simp only [UInt256.val, ZMod.val_hmul, ZMod.hmul_ne_zero_iff] at *
            rw [nonpos_iff_eq_zero, ZMod.val_eq_zero] at h₃; cases h₃
            simp at h₄ ⊢
            rw [ZMod.hmul_eq_zero_iff] at h₁
            rw [ZMod.val_mul_of_lt h₁] at h
            apply Nat.lt_of_div_lt_div (k := U128_MOD)
            rw [mul_add, Nat.add_div U128_MOD_pos]
            have : ¬ U128_MOD ≤ ZMod.val aₗ * (U128_MOD * ZMod.val bₕ) % U128_MOD
                + ZMod.val aₗ * ZMod.val bₗ % U128_MOD := by
              rw [not_le, mul_comm U128_MOD, ← mul_assoc, Nat.mul_mod_left, zero_add]
              apply Nat.mod_lt _ U128_MOD_pos
            simp only [this, ite_false, add_zero, U256_MOD_div, gt_iff_lt]
            rwa [mul_comm U128_MOD, ← mul_assoc, Nat.mul_div_cancel _ U128_MOD_pos, add_comm]
          · simp only [UInt256.mul_def, Prod.mk.injEq, Bool.toSierraBool_decide_inr', true_and]
            simp only [UInt256.val, ZMod.val_hmul, ZMod.hmul_ne_zero_iff] at *
            replace h₄ := Nat.mul_le_mul_right U128_MOD h₄
            rw [U128_MOD_mul_U128_MOD] at h₄
            apply le_trans h₄ _
            ring_nf
            apply le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (ZMod.val_mul_le _ _)) _)
            apply le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (ZMod.val_add_le _ _)) _)
            rw [ZMod.val_hmul, add_mul]
            apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.div_mul_le_self _ _) _) _)
            apply le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ (ZMod.val_mul_le _ _)) _) _) _
            ring_nf
            simp only [le_add_iff_nonneg_right, zero_le]
        · rcases h₄ with (⟨h₄,rfl⟩|⟨h₄,rfl⟩)
          · sorry
          · simp only [UInt256.mul_def, Prod.mk.injEq, Bool.toSierraBool_decide_inr', true_and]
            simp only [UInt256.val, ZMod.val_hmul, ZMod.hmul_ne_zero_iff] at *
            rw [add_mul, mul_add, mul_add]
            apply Nat.le_add_of_le_left; apply Nat.le_add_of_le_left
            ring_nf
            rw [mul_assoc, pow_two, U128_MOD_mul_U128_MOD]
            apply Nat.le_mul_of_pos_right
            simp only [zero_lt_mul_left, h₃, h₄]
            sorry
      · simp only [UInt256.mul_def, Prod.mk.injEq, Bool.toSierraBool_decide_inr', true_and]
        simp only [UInt256.val, ZMod.val_hmul, ZMod.hmul_ne_zero_iff] at *
        ring_nf
        apply Nat.le_add_of_le_left; apply Nat.le_add_of_le_left; apply Nat.le_add_of_le_left
        rw [mul_assoc, ← U128_MOD_mul_U128_MOD]
        apply Nat.mul_le_mul_left _ h₂
    · simp only [UInt256.mul_def, Prod.mk.injEq, Bool.toSierraBool_decide_inr', true_and]
      simp only [UInt256.val, ZMod.val_hmul, ZMod.hmul_ne_zero_iff] at *
      ring_nf
      apply Nat.le_add_of_le_left; apply Nat.le_add_of_le_left; apply Nat.le_add_of_le_right
      rw [mul_assoc, ← U128_MOD_mul_U128_MOD]
      apply Nat.mul_le_mul_left _ h₁
  · simp only [UInt256.mul_def, Prod.mk.injEq, Bool.toSierraBool_decide_inr', true_and]
    simp only [UInt256.val, ZMod.val_hmul] at *
    replace h := Nat.mul_le_mul_right U128_MOD h
    rw [add_mul, U128_MOD_mul_U128_MOD] at h; apply le_trans h; clear h
    apply le_trans (Nat.add_le_add_right (Nat.div_mul_le_self _ _) _)
    apply le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (ZMod.val_mul_le _ _)) _)
    ring_nf
    rw [add_assoc]
    simp only [le_add_iff_nonneg_right, zero_le]

aegis_spec "core::integer::u256_checked_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  (a.val * b.val < U256_MOD ∧ ρ = .inl (a * b)) ∨ (U256_MOD ≤ a.val * b.val ∧ ρ = .inr ())

aegis_prove "core::integer::u256_checked_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold «spec_core::integer::u256_checked_mul»
  sierra_simp'
  aesop

aegis_spec "core::integer::U256Mul::mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  (a.val * b.val < U256_MOD ∧ ρ = .inl (a * b)) ∨ (U256_MOD ≤ a.val * b.val ∧ ρ.isRight)

aegis_prove "core::integer::U256Mul::mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold «spec_core::integer::U256Mul::mul»
  rintro ⟨_,_,_,(⟨h,rfl⟩|⟨h,rfl⟩),(⟨h',rfl⟩|⟨h',rfl⟩)⟩
  <;> aesop

aegis_spec "core::integer::U256PartialOrd::lt" :=
  fun _ _ (a b : UInt256) _ ρ =>
  ρ = Bool.toSierraBool (a.val < b.val)

aegis_prove "core::integer::U256PartialOrd::lt" :=
  fun _ _ (a b : UInt256) _ ρ => by
  unfold «spec_core::integer::U256PartialOrd::lt»
  sierra_simp'
  rintro ⟨aₗ,aₕ,bₗ,bₕ,rfl,rfl,(⟨hle,h⟩|⟨h,rfl⟩)⟩
  · rcases h with (⟨h,rfl⟩|⟨rfl,(⟨h,rfl⟩|⟨h,rfl⟩)⟩)
    · simp only [UInt256.val]
      rw [← @ne_eq] at h
      have := lt_of_le_of_ne hle ((ZMod.val_injective _).ne h.symm)
      rw [Bool.toSierraBool_decide_inl', not_lt]
      apply le_trans _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _)
      rw [Nat.mul_succ, add_assoc]
      apply Nat.add_le_add_left
      apply le_of_lt
      apply lt_of_lt_of_le bₗ.val_lt
      simp
    · simp [UInt256.val]
  · simp only [UInt256.val]
    rw [Bool.toSierraBool_decide_inr']
    apply lt_of_lt_of_le _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _)
    rw [Nat.mul_succ, add_assoc]
    apply Nat.add_lt_add_left
    apply lt_of_lt_of_le aₗ.val_lt
    simp

#exit

aegis_info "core::integer::u256_safe_div_rem"

aegis_spec "core::integer::u256_safe_div_rem" :=
  fun _ _ (a b : UInt256) _ ρ =>
  True

aegis_prove "core::integer::u256_safe_div_rem" :=
  fun _ _ (a b : UInt256) _ ρ => by
  sorry

#check ZMod.ndiv

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u256>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u256>>::expect" :=
  fun _ a err ρ => by
  unfold «spec_core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u256>>::expect»
  aesop

aegis_spec "core::integer::U256Div::div" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  (b ≠ 0 ∧ ∃ c, ρ = .inl c ∧ c.val = a.val / b.val) ∨ (b = 0 ∧ ρ.isRight) -- TODO

aegis_prove "core::integer::U256Div::div" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold «spec_core::integer::U256Div::div»
  simp only [UInt256.val, UInt256.zero_def]
  rcases b with ⟨bₗ,bₕ⟩; dsimp only
  rintro ⟨_,_,_,_,_,_,_,(⟨h,rfl⟩|⟨rfl,rfl,h⟩),h'⟩
  · left
    rcases h' with (⟨he,h'⟩|h')
    · injection he with he; cases he
      rcases h' with (⟨he,h',-,rfl⟩|h')
      · injection he with he; cases he
        constructor
        · intro h; injection h; simp_all
        · exact ⟨_,rfl,h'⟩
      · simp at h'
    · simp at h'
  · right; aesop
