import CorelibVerification.Aux.ZMod
import CorelibVerification.Corelib.Result
import CorelibVerification.Aux.UInt256
import CorelibVerification.Aux.Bool
import CorelibVerification.Aux.BitVec
import Aegis.Tactic

open Sierra

syntax "sierra_simp'" : tactic
macro_rules
| `(tactic|sierra_simp') =>
  `(tactic|
    simp only [Prod.mk_inj, and_assoc, Bool.coe_toSierraBool, Bool.toSierraBool_coe,
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
  fun _ _ _ _ =>
  True

aegis_prove "core::integer::U128MulGuaranteeDestruct::destruct" :=
   fun _ _ _ _ _ =>
   True.intro

aegis_spec "core::result::ResultTraitImpl<core::integer::u8, core::integer::u8>::expect<core::integer::u8Drop>" :=
  fun _ a b ρ =>
  ρ = Sum.map id (fun _ => ((), [b])) a

aegis_prove "core::result::ResultTraitImpl<core::integer::u8, core::integer::u8>::expect<core::integer::u8Drop>" :=
  fun _ a b ρ => by
  unfold_spec "core::result::ResultTraitImpl<core::integer::u8, core::integer::u8>::expect<core::integer::u8Drop>"
  rintro ⟨_, _, _, _, (⟨rfl, rfl⟩|⟨h⟩)⟩
  · aesop
  · aesop

aegis_spec "core::integer::U8Sub::sub" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.usubOverflow a b ∧ ρ = .inl (a - b) ∨
    BitVec.usubOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U8Sub::sub" := fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U8Sub::sub"
  aesop

instance U128_MOD_lt_PRIME : Fact (U128_MOD < PRIME) := ⟨by norm_num [U128_MOD, PRIME]⟩

instance : NeZero U8_MOD := ⟨by norm_num [U8_MOD]⟩

instance : NeZero U16_MOD := ⟨by norm_num [U16_MOD]⟩

instance : NeZero U32_MOD := ⟨by norm_num [U32_MOD]⟩

instance : NeZero U64_MOD := ⟨by norm_num [U64_MOD]⟩

instance : NeZero U128_MOD := ⟨by norm_num [U128_MOD]⟩

theorem U8_MOD_lt_U16_MOD : U8_MOD < U16_MOD := by norm_num [U8_MOD, U16_MOD]

theorem U16_MOD_lt_U32_MOD : U16_MOD < U32_MOD := by norm_num [U16_MOD, U32_MOD]

theorem U32_MOD_lt_U64_MOD : U32_MOD < U64_MOD := by norm_num [U32_MOD, U64_MOD]

theorem U64_MOD_lt_U128_MOD : U64_MOD < U128_MOD := by norm_num [U64_MOD, U128_MOD]

theorem U8_MOD_pos : 0 < U8_MOD := by norm_num [U8_MOD]

theorem U16_MOD_pos : 0 < U16_MOD := by norm_num [U16_MOD]

theorem U32_MOD_pos : 0 < U32_MOD := by norm_num [U32_MOD]

theorem U64_MOD_pos : 0 < U64_MOD := by norm_num [U64_MOD]

aegis_spec "core::integer::u128_wide_mul" :=
  fun _ _ a b _ ρ =>
  ρ = ((a.zeroExtend 256 * b.zeroExtend 256).extractLsb' 128 128,
    (a.zeroExtend 256 * b.zeroExtend 256).extractLsb' 0 128)

aegis_prove "core::integer::u128_wide_mul" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::u128_wide_mul"
  rintro ⟨w₁,w₂,h₁,rfl⟩
  congr <;> bv_decide

aegis_spec "core::integer::u128_checked_mul" :=
  fun _ _ a b  _ ρ =>
  a.toNat * b.toNat < U128_MOD ∧ ρ = .inl (a * b) ∨
    U128_MOD ≤ a.toNat * b.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::u128_checked_mul" :=
  fun _ _ a b  _ ρ => by
  unfold_spec "core::integer::u128_checked_mul"
  simp only [Prod.mk.injEq, ne_eq, forall_exists_index, and_imp]
  rintro _ _ rfl rfl (⟨h,rfl⟩|⟨h,rfl⟩)
  · left
    simp
    constructor
    · simp at h
      rw [ZMod.castLE_eq_zero_iff_eq_zero, ← BitVec.toFin_zero (w := 128), BitVec.toFin_inj] at h
      simp [BitVec.toNat_eq, BitVec.extractLsb'_toNat, BitVec.toNat_mul] at h
      have alt : a.toNat < 2 ^ 128 := by exact BitVec.isLt a
      have blt : b.toNat < 2 ^ 128 := by exact BitVec.isLt b
      have : BitVec.toNat a * BitVec.toNat b < 2 ^ 256 := by
        have : 2 ^ 256 = 2 ^ 128 * 2 ^ 128 := by rfl
        rw [this]
        apply Nat.mul_lt_mul''
        <;> omega
      unfold U128_MOD
      omega
    · bv_decide
  · right
    rw [ZMod.castLE_eq_zero_iff_eq_zero, ← BitVec.toFin_zero (w := 128), BitVec.toFin_inj] at h
    constructor
    · simp [BitVec.toNat_eq, BitVec.extractLsb'_toNat, BitVec.toNat_mul] at h
      unfold U128_MOD
      omega
    · rfl

aegis_spec "core::option::OptionTraitImpl<core::integer::u8>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u8>::expect" :=
  fun _ a b ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::integer::u8>::expect"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::integer::u16>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u16>::expect" :=
  fun _ a b ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::integer::u16>::expect"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::integer::u32>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u32>::expect" :=
  fun _ a b ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::integer::u32>::expect"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::integer::u64>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u64>::expect" :=
  fun _ a b ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::integer::u64>::expect"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::integer::u128>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u128>::expect" :=
  fun _ a b ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::integer::u128>::expect"
  aesop

aegis_spec "core::integer::DowncastableIntTryInto::<core::integer::u16, core::integer::u8, core::integer::DowncastableU16, core::integer::DowncastableU8, _>::try_into" :=
  fun _ _ a _ ρ =>
  a.toNat < U8_MOD ∧ ρ = .inl (a.truncate 8) ∨
    U8_MOD ≤ a.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::DowncastableIntTryInto::<core::integer::u16, core::integer::u8, core::integer::DowncastableU16, core::integer::DowncastableU8, _>::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::DowncastableIntTryInto::<core::integer::u16, core::integer::u8, core::integer::DowncastableU16, core::integer::DowncastableU8, _>::try_into"
  aesop

aegis_spec "core::integer::DowncastableIntTryInto::<core::integer::u32, core::integer::u16, core::integer::DowncastableU32, core::integer::DowncastableU16, _>::try_into" :=
  fun _ _ a _ ρ =>
  a.toNat < U16_MOD ∧ ρ = .inl (a.truncate 16) ∨
    U16_MOD ≤ a.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::DowncastableIntTryInto::<core::integer::u32, core::integer::u16, core::integer::DowncastableU32, core::integer::DowncastableU16, _>::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::DowncastableIntTryInto::<core::integer::u32, core::integer::u16, core::integer::DowncastableU32, core::integer::DowncastableU16, _>::try_into"
  aesop

aegis_spec "core::integer::DowncastableIntTryInto::<core::integer::u64, core::integer::u32, core::integer::DowncastableU64, core::integer::DowncastableU32, _>::try_into" :=
 fun _ _ a _ ρ =>
 a.toNat < U32_MOD ∧ ρ = .inl (a.truncate 32) ∨
   U32_MOD ≤ a.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::DowncastableIntTryInto::<core::integer::u64, core::integer::u32, core::integer::DowncastableU64, core::integer::DowncastableU32, _>::try_into" :=
 fun _ _ a _ ρ => by
 unfold_spec "core::integer::DowncastableIntTryInto::<core::integer::u64, core::integer::u32, core::integer::DowncastableU64, core::integer::DowncastableU32, _>::try_into"
 aesop

aegis_spec "core::integer::DowncastableIntTryInto::<core::integer::u128, core::integer::u64, core::integer::DowncastableU128, core::integer::DowncastableU64, _>::try_into" :=
 fun _ _ a _ ρ =>
 a.toNat < U64_MOD ∧ ρ = .inl (a.truncate 64) ∨
   U64_MOD ≤ a.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::DowncastableIntTryInto::<core::integer::u128, core::integer::u64, core::integer::DowncastableU128, core::integer::DowncastableU64, _>::try_into" :=
 fun _ _ a _ ρ => by
 unfold_spec "core::integer::DowncastableIntTryInto::<core::integer::u128, core::integer::u64, core::integer::DowncastableU128, core::integer::DowncastableU64, _>::try_into"
 aesop

aegis_spec "core::integer::U8Mul::mul" :=
  fun _ _ a b _ ρ =>
  a.toNat * b.toNat < U8_MOD ∧ ρ = .inl (a * b) ∨
    U8_MOD ≤ a.toNat * b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U8Mul::mul" := fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U8Mul::mul"
  have := Nat.mul_lt_mul'' a.isLt b.isLt
  intro h_auto
  simp_all only [Nat.reducePow, Nat.reduceMul, BitVec.truncate_eq_setWidth, BitVec.toNat_mul, BitVec.toNat_setWidth,
    Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt, U8_MOD, Int.cast_ofNat, Sum.exists, Sum.inl.injEq,
    reduceCtorEq, and_false, or_false, Sum.map_inl, id_eq, existsAndEq, and_true, false_or, Sum.map_inr, exists_const]
  cases h_auto with
  | inl h =>
    simp_all only [true_and]
    obtain ⟨_, rfl⟩ := h
    simp_all only [Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false]
    bv_decide
  | inr h_1 =>
    simp_all only [true_and]
    obtain ⟨_, rfl⟩ := h_1
    simp_all only [reduceCtorEq, and_false, Sum.isRight_inr, or_true]

aegis_spec "core::integer::U16Mul::mul" :=
  fun _ _ a b _ ρ =>
  a.toNat * b.toNat < U16_MOD ∧ ρ = .inl (a * b) ∨
    U16_MOD ≤ a.toNat * b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U16Mul::mul" := fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U16Mul::mul"
  have := Nat.mul_lt_mul'' a.isLt b.isLt
  intro h_auto
  simp_all only [Nat.reducePow, Nat.reduceMul, BitVec.truncate_eq_setWidth, BitVec.toNat_mul, BitVec.toNat_setWidth,
    Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt, Int.cast_ofNat, Sum.exists, Sum.inl.injEq, reduceCtorEq,
    and_false, or_false, Sum.map_inl, id_eq, existsAndEq, and_true, false_or, Sum.map_inr, exists_const]
  cases h_auto with
  | inl h =>
    simp_all only [true_and]
    rcases h.2
    simp_all only [Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false]
    bv_decide
  | inr h_1 =>
    simp_all only [true_and]
    rcases h_1.2
    simp_all only [reduceCtorEq, and_false, Sum.isRight_inr, or_true]

aegis_spec "core::integer::U32Mul::mul" :=
  fun _ _ a b _ ρ =>
  a.toNat * b.toNat < U32_MOD ∧ ρ = .inl (a * b) ∨
    U32_MOD ≤ a.toNat * b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U32Mul::mul" := fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U32Mul::mul"
  have := Nat.mul_lt_mul'' a.isLt b.isLt
  intro h_auto
  simp_all only [Nat.reducePow, Nat.reduceMul, BitVec.truncate_eq_setWidth, BitVec.toNat_mul, BitVec.toNat_setWidth,
    Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt, Int.cast_ofNat, Sum.exists, Sum.inl.injEq, reduceCtorEq,
    and_false, or_false, Sum.map_inl, id_eq, existsAndEq, and_true, false_or, Sum.map_inr, exists_const]
  cases h_auto with
  | inl h =>
    simp_all only [true_and]
    rcases h.2
    simp_all only [Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false]
    bv_decide
  | inr h_1 =>
    simp_all only [true_and]
    rcases h_1.2
    simp_all only [reduceCtorEq, and_false, Sum.isRight_inr, or_true]

aegis_spec "core::integer::U64Mul::mul" :=
  fun _ _ a b _ ρ =>
  a.toNat * b.toNat < U64_MOD ∧ ρ = .inl (a * b) ∨
    U64_MOD ≤ a.toNat * b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U64Mul::mul" := fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U64Mul::mul"
  have := Nat.mul_lt_mul'' a.isLt b.isLt
  intro h_auto
  simp_all only [Nat.reducePow, Nat.reduceMul, BitVec.truncate_eq_setWidth, BitVec.toNat_mul, BitVec.toNat_setWidth,
    Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt, Int.cast_ofNat, Sum.exists, Sum.inl.injEq, reduceCtorEq,
    and_false, or_false, Sum.map_inl, id_eq, existsAndEq, and_true, false_or, Sum.map_inr, exists_const]
  cases h_auto with
  | inl h =>
    simp_all only [true_and]
    rcases h.2
    simp_all only [Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false]
    bv_decide
  | inr h_1 =>
    simp_all only [true_and]
    rcases h_1.2
    simp_all only [reduceCtorEq, and_false, Sum.isRight_inr, or_true]

aegis_spec "core::integer::U128Mul::mul" :=
  fun _ _ a b _ ρ =>
  a.toNat * b.toNat < U128_MOD ∧ ρ = .inl (a * b) ∨
    U128_MOD ≤ a.toNat * b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U128Mul::mul" := fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U128Mul::mul"
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u16, core::integer::u16>::expect<core::integer::u16Drop>" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::result::ResultTraitImpl<core::integer::u16, core::integer::u16>::expect<core::integer::u16Drop>" :=
  fun _ a err ρ => by
  unfold_spec "core::result::ResultTraitImpl<core::integer::u16, core::integer::u16>::expect<core::integer::u16Drop>"
  aesop

aegis_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::integer::u128Drop>" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::integer::u128Drop>" :=
  fun _ a err ρ => by
  unfold_spec "core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::integer::u128Drop>"
  aesop

aegis_spec "core::integer::U128Sub::sub" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.usubOverflow a b ∧ ρ = .inl (a - b) ∨
    BitVec.usubOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U128Sub::sub" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U128Sub::sub"
  aesop

aegis_spec "core::integer::u128_try_from_felt252" :=
  fun _ _ a _ ρ =>
  a.val < U128_MOD ∧ ρ = .inl (.ofNat _ a.val) ∨
    U128_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "core::integer::u128_try_from_felt252" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::u128_try_from_felt252"
  aesop

aegis_spec "core::integer::BoundedU128::max" :=
  fun _ ρ =>
  ρ = 340282366920938463463374607431768211455

aegis_prove "core::integer::BoundedU128::max" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U128BitNot::bitnot" :=
  fun _ _ a _ ρ =>
  ρ = .inl (~~~ a)

aegis_prove "core::integer::U128BitNot::bitnot" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::U128BitNot::bitnot"
  aesop (add safe (by bv_decide))

aegis_spec "core::integer::u8_try_as_non_zero" :=
  fun _ a ρ =>
  a = 0 ∧ ρ = .inr () ∨
    a ≠ 0 ∧ ρ = .inl a

aegis_prove "core::integer::u8_try_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u8_try_as_non_zero"
  aesop

aegis_spec "core::integer::u16_try_as_non_zero" :=
  fun _ a ρ =>
  a = 0 ∧ ρ = .inr () ∨
    a ≠ 0 ∧ ρ = .inl a

aegis_prove "core::integer::u16_try_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u16_try_as_non_zero"
  aesop

aegis_spec "core::integer::u32_try_as_non_zero" :=
  fun _ a ρ =>
  a = 0 ∧ ρ = .inr ()
    ∨ a ≠ 0 ∧ ρ = .inl a

aegis_prove "core::integer::u32_try_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u32_try_as_non_zero"
  aesop

aegis_spec "core::integer::u64_try_as_non_zero" :=
  fun _ a ρ =>
  a = 0 ∧ ρ = .inr ()
    ∨ a ≠ 0 ∧ ρ = .inl a

aegis_prove "core::integer::u64_try_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u64_try_as_non_zero"
  aesop

aegis_spec "core::integer::u128_try_as_non_zero" :=
  fun _ a ρ =>
  (a = 0 ∧ ρ = .inr ()) ∨ (a ≠ 0 ∧ ρ = .inl a)

aegis_prove "core::integer::u128_try_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u128_try_as_non_zero"
  aesop

aegis_spec "core::integer::u256_try_as_non_zero" :=
  fun _ a ρ =>
  a = (0, 0) ∧ ρ = .inr () ∨
   ((a.1 ≠ 0) ∨ (a.2 ≠ 0)) ∧ ρ = .inl a

aegis_prove "core::integer::u256_try_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u256_try_as_non_zero"
  intro h_auto
  simp_all only [BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.append_eq, ne_eq]
  obtain ⟨fst, snd⟩ := a
  simp_all only [Prod.mk.injEq]
  cases h_auto with
  | inl h => simp_all only [and_self, not_true_eq_false, or_self, false_and, or_false]
  | inr h_1 =>
    simp_all only [and_true]
    obtain ⟨left, right⟩ := h_1
    subst right
    simp_all only [reduceCtorEq, and_false, false_or]
    bv_decide

aegis_spec "core::integer::u64_as_non_zero" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::u64_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u64_as_non_zero"
  aesop

aegis_spec "core::integer::u128_as_non_zero" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::u128_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u128_as_non_zero"
  aesop

aegis_spec "core::integer::u256_as_non_zero" :=
  fun _ a ρ =>
  (a.1 ≠ 0 ∨ a.2 ≠ 0) ∧ ρ = .inl a ∨
    a = (0, 0) ∧ ρ.isRight

aegis_prove "core::integer::u256_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u256_as_non_zero"
  aesop

aegis_spec "core::integer::u256_from_felt252" :=
  fun _ _ a _ (ρ : UInt256) =>
  ρ = .ofBitVec (.ofNat _ a.val)

aegis_prove "core::integer::u256_from_felt252" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::u256_from_felt252"
  haveI : NeZero U128_MOD := ⟨by norm_num [U128_MOD]⟩
  rintro ⟨_,_,(⟨h,rfl⟩|⟨-,h₂,rfl⟩)⟩
  · simp only [UInt256.ofBitVec, BitVec.natCast_eq_ofNat]
    rw [← BitVec.setWidth_ofNat_of_le (show 128 ≤ 256 by omega) a.val]
    apply Prod.ext
    · bv_decide
    · simp [U128_MOD] at *
      rw [BitVec.extractLsb'.eq_1]
      simp
      rw [Nat.mod_eq_of_lt (h.trans (by omega)), Nat.shiftRight_eq_zero _ _ h]
  · simp at h₂
    ext1
    simpa

aegis_spec "core::integer::U64TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::U64TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold_spec "core::integer::U64TryIntoNonZero::try_into"
  aesop

aegis_spec "core::integer::U128TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::U128TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold_spec "core::integer::U128TryIntoNonZero::try_into"
  aesop

aegis_spec "core::integer::U256TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  (a.1 ≠ 0 ∨ a.2 ≠ 0) ∧ ρ = .inl a ∨
    a.1 = 0 ∧ a.2 = 0 ∧ ρ.isRight

aegis_prove "core::integer::U256TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold_spec "core::integer::U256TryIntoNonZero::try_into"
  rintro ⟨_,(⟨h,rfl⟩|h),h'⟩
  · rcases h' with (⟨h',rfl⟩|h'); aesop
  · aesop

aegis_spec "core::integer::Felt252TryIntoU8::try_into" :=
  fun _ _ a _ ρ =>
  a.val < U8_MOD ∧ ρ = .inl (.ofNat _ a.val) ∨
    U8_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::integer::Felt252TryIntoU8::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::Felt252TryIntoU8::try_into"
  aesop

aegis_spec "core::integer::Felt252TryIntoU16::try_into" :=
  fun _ _ a _ ρ =>
  a.val < U16_MOD ∧ ρ = .inl (.ofNat _ a.val) ∨
    U16_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::integer::Felt252TryIntoU16::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::Felt252TryIntoU16::try_into"
  aesop

aegis_spec "core::integer::Felt252TryIntoU32::try_into" :=
  fun _ _ a _ ρ =>
  a.val < U32_MOD ∧ ρ = .inl (.ofNat _ a.val) ∨
    U32_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::integer::Felt252TryIntoU32::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::Felt252TryIntoU32::try_into"
  aesop

aegis_spec "core::integer::Felt252TryIntoU64::try_into" :=
  fun _ _ a _ ρ =>
  a.val < U64_MOD ∧ ρ = .inl (.ofNat _ a.val) ∨
   U64_MOD ≤ a.val ∧ ρ.isRight

aegis_prove "core::integer::Felt252TryIntoU64::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::Felt252TryIntoU64::try_into"
  aesop

aegis_spec "core::integer::U8Add::add" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.uaddOverflow a b ∧ ρ = .inl (a + b) ∨
    BitVec.uaddOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U8Add::add" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U8Add::add"
  aesop

aegis_spec "core::integer::U16Add::add" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.uaddOverflow a b ∧ ρ = .inl (a + b) ∨
    BitVec.uaddOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U16Add::add" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U16Add::add"
  aesop

aegis_spec "core::integer::U16Sub::sub" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.usubOverflow a b ∧ ρ = .inl (a - b) ∨
    BitVec.usubOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U16Sub::sub" :=
   fun _ _ a b _ ρ => by
   unfold_spec "core::integer::U16Sub::sub"
   aesop

aegis_spec "core::integer::U32Add::add" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.uaddOverflow a b ∧ ρ = .inl (a + b) ∨
    BitVec.uaddOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U32Add::add" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U32Add::add"
  aesop

aegis_spec "core::integer::U32Sub::sub" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.usubOverflow a b ∧ ρ = .inl (a - b) ∨
    BitVec.usubOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U32Sub::sub" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U32Sub::sub"
  aesop

aegis_spec "core::integer::U64Add::add" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.uaddOverflow a b ∧ ρ = .inl (a + b) ∨
    BitVec.uaddOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U64Add::add" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U64Add::add"
  aesop

aegis_spec "core::integer::U64Sub::sub" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.usubOverflow a b ∧ ρ = .inl (a - b) ∨
    BitVec.usubOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U64Sub::sub" :=
   fun _ _ a b _ ρ => by
   unfold_spec "core::integer::U64Sub::sub"
   aesop

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u8>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u8>>::expect" :=
  fun _ a err ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u8>>::expect"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u16>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u16>>::expect" :=
  fun _ a err ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u16>>::expect"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u32>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u32>>::expect" :=
  fun _ a err ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u32>>::expect"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u64>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u64>>::expect" :=
  fun _ a err ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u64>>::expect"
  aesop

aegis_spec "core::integer::u8_as_non_zero" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::u8_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u8_as_non_zero"
  aesop

aegis_spec "core::integer::u16_as_non_zero" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::u16_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u16_as_non_zero"
  aesop

aegis_spec "core::integer::u32_as_non_zero" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::u32_as_non_zero" :=
  fun _ a ρ => by
  unfold_spec "core::integer::u32_as_non_zero"
  aesop

aegis_spec "core::integer::U8TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::U8TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold_spec "core::integer::U8TryIntoNonZero::try_into"
  aesop

aegis_spec "core::integer::U16TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
     a = 0 ∧ ρ.isRight

aegis_prove "core::integer::U16TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold_spec "core::integer::U16TryIntoNonZero::try_into"
  aesop

aegis_spec "core::integer::U32TryIntoNonZero::try_into" :=
  fun _ a ρ =>
  a ≠ 0 ∧ ρ = .inl a ∨
    a = 0 ∧ ρ.isRight

aegis_prove "core::integer::U32TryIntoNonZero::try_into" :=
  fun _ a ρ => by
  unfold_spec "core::integer::U32TryIntoNonZero::try_into"
  aesop

aegis_spec "core::integer::U8DivRem::div_rem" :=
  fun _ _ a b _ ρ =>
  ρ = (a.udiv b, a.umod b)

aegis_prove "core::integer::U8DivRem::div_rem" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U16DivRem::div_rem" :=
  fun _ _ a b _ ρ =>
  ρ = (a.udiv b, a.umod b)

aegis_prove "core::integer::U16DivRem::div_rem" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U32DivRem::div_rem" :=
  fun _ _ a b _ ρ =>
  ρ = (a.udiv b, a.umod b)

aegis_prove "core::integer::U32DivRem::div_rem" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U64DivRem::div_rem" :=
  fun _ _ a b _ ρ =>
  ρ = (a.udiv b, a.umod b)

aegis_prove "core::integer::U64DivRem::div_rem" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U128DivRem::div_rem" :=
  fun _ _ a b _ ρ =>
  ρ = (a.udiv b, a.umod b)

aegis_prove "core::integer::U128DivRem::div_rem" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::by_div_rem::DivImpl::<core::integer::u8, core::integer::U8DivRem, core::integer::U8TryIntoNonZero, core::integer::u8Drop>::div" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (a.udiv b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::DivImpl::<core::integer::u8, core::integer::U8DivRem, core::integer::U8TryIntoNonZero, core::integer::u8Drop>::div" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::DivImpl::<core::integer::u8, core::integer::U8DivRem, core::integer::U8TryIntoNonZero, core::integer::u8Drop>::div"
  aesop

aegis_spec "core::integer::by_div_rem::DivImpl::<core::integer::u16, core::integer::U16DivRem, core::integer::U16TryIntoNonZero, core::integer::u16Drop>::div" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (a.udiv b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::DivImpl::<core::integer::u16, core::integer::U16DivRem, core::integer::U16TryIntoNonZero, core::integer::u16Drop>::div" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::DivImpl::<core::integer::u16, core::integer::U16DivRem, core::integer::U16TryIntoNonZero, core::integer::u16Drop>::div"
  aesop

aegis_spec "core::integer::by_div_rem::DivImpl::<core::integer::u32, core::integer::U32DivRem, core::integer::U32TryIntoNonZero, core::integer::u32Drop>::div" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (a.udiv b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::DivImpl::<core::integer::u32, core::integer::U32DivRem, core::integer::U32TryIntoNonZero, core::integer::u32Drop>::div" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::DivImpl::<core::integer::u32, core::integer::U32DivRem, core::integer::U32TryIntoNonZero, core::integer::u32Drop>::div"
  aesop

aegis_spec "core::integer::by_div_rem::DivImpl::<core::integer::u64, core::integer::U64DivRem, core::integer::U64TryIntoNonZero, core::integer::u64Drop>::div" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (a.udiv b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::DivImpl::<core::integer::u64, core::integer::U64DivRem, core::integer::U64TryIntoNonZero, core::integer::u64Drop>::div" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::DivImpl::<core::integer::u64, core::integer::U64DivRem, core::integer::U64TryIntoNonZero, core::integer::u64Drop>::div"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u128>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u128>>::expect" :=
  fun _ a err ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u128>>::expect"
  aesop

aegis_spec "core::integer::by_div_rem::DivImpl::<core::integer::u128, core::integer::U128DivRem, core::integer::U128TryIntoNonZero, core::integer::u128Drop>::div" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (a.udiv b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::DivImpl::<core::integer::u128, core::integer::U128DivRem, core::integer::U128TryIntoNonZero, core::integer::u128Drop>::div" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::DivImpl::<core::integer::u128, core::integer::U128DivRem, core::integer::U128TryIntoNonZero, core::integer::u128Drop>::div"
  aesop

aegis_spec "core::integer::U128Add::add" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.uaddOverflow a b ∧ ρ = .inl (a + b) ∨
    BitVec.uaddOverflow a b ∧ ρ.isRight

aegis_prove "core::integer::U128Add::add" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U128Add::add"
  aesop

aegis_spec "core::integer::u256_overflowing_add" :=
  fun _ _ (a b : UInt256) _ ρ =>
  ρ = (a + b, Bool.toSierraBool (U256_MOD ≤ a.toNat + b.toNat))

aegis_prove "core::integer::u256_overflowing_add" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::u256_overflowing_add"
  aesop (add simp [U128_MOD, U256_MOD, Nat.mod_eq_of_lt, UInt256.pair_toNat])
    (config := { warnOnNonterminal := .false })
    <;> omega  -- TODO inline omega into `aesop`

aegis_spec "core::integer::u256_checked_add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) =>
  a.toNat + b.toNat < U256_MOD ∧ ρ = .inl (a + b) ∨
    U256_MOD ≤ a.toNat + b.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::u256_checked_add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) => by
  unfold_spec "core::integer::u256_checked_add"
  rintro ⟨_,_,_,_,he,(⟨h,rfl⟩|h)⟩
  · aesop
  · aesop

aegis_spec "core::option::OptionTraitImpl<core::integer::u256>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::integer::u256>::expect" :=
  fun _ a err ρ => by
  unfold_spec  "core::option::OptionTraitImpl<core::integer::u256>::expect"
  aesop

aegis_spec "core::integer::U256Add::add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  a.toNat + b.toNat < U256_MOD ∧ ρ = .inl (a + b) ∨
    U256_MOD ≤ a.toNat + b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U256Add::add" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold_spec "core::integer::U256Add::add"
  aesop

aegis_spec "core::integer::u256_overflow_sub" :=
  fun _ _ (a b : UInt256) _ ρ =>
  ρ = (a - b, Bool.toSierraBool (a.toNat < b.toNat))

aegis_prove "core::integer::u256_overflow_sub" :=
  fun _ _ (a b : UInt256) _ ρ => by
  unfold_spec  "core::integer::u256_overflow_sub"
  aesop (add simp [UInt256.pair_toNat, U128_MOD])
    (config := { warnOnNonterminal := .false })
    <;> omega  -- TODO inline `omega` application into `aesop`

aegis_spec "core::integer::u256_checked_sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) =>
  b.toNat ≤ a.toNat ∧ ρ = .inl (a - b) ∨
    a.toNat < b.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::u256_checked_sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ Unit) => by
  unfold_spec "core::integer::u256_checked_sub"
  rintro ⟨_,_,_,_,he,(⟨h,rfl⟩|h)⟩
  · aesop
  · aesop

aegis_spec "core::integer::U256Sub::sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  b.toNat ≤ a.toNat ∧ ρ = .inl (a - b) ∨
    a.toNat < b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U256Sub::sub" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold_spec "core::integer::U256Sub::sub"
  aesop

aegis_spec "core::integer::U128PartialEq::eq" :=
  fun _ a b ρ =>
  ρ = (Bool.toSierraBool (a = b))

aegis_prove "core::integer::U128PartialEq::eq" :=
  fun _ a b ρ => by
  unfold_spec "core::integer::U128PartialEq::eq"
  aesop

aegis_spec "core::integer::U128PartialEq::ne" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a ≠ b)

aegis_prove "core::integer::U128PartialEq::ne" :=
  fun _ a b ρ => by
  unfold_spec "core::integer::U128PartialEq::ne"
  rintro rfl
  simp_all

aegis_spec "core::integer::U128PartialOrd::gt" :=
  fun _ _ a b _ ρ =>
  ρ = Bool.toSierraBool (b < a)

aegis_prove "core::integer::U128PartialOrd::gt" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U128PartialOrd::gt"
  aesop

aegis_spec "core::integer::U128PartialOrd::lt" :=
  fun _ _ a b _ ρ =>
  ρ = Bool.toSierraBool (a < b)

aegis_prove "core::integer::U128PartialOrd::lt" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U128PartialOrd::lt"
  aesop

theorem U128_MOD_mul_U128_MOD : U128_MOD * U128_MOD = U256_MOD := rfl

theorem U256_MOD_div_U128_MOD : U256_MOD / U128_MOD = U128_MOD := rfl

theorem U128_MOD_pos : 0 < U128_MOD := by norm_num [U128_MOD]

aegis_spec "core::integer::u256_overflow_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 × _) =>
  ρ = (a * b, Bool.toSierraBool (U256_MOD ≤ a.toNat * b.toNat))

-- TODO: Come back to this when we have `BitVec.umulOverflow`.
aegis_prove "core::integer::u256_overflow_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 × _) => by
  rcases a with ⟨aₗ, aₕ⟩
  rcases b with ⟨bₗ, bₕ⟩
  unfold_spec "core::integer::u256_overflow_mul"
  rintro ⟨_,_,_,_,_,_,_,_,h⟩
  rcases h with ⟨_,_,_,_,_,_,_,_,h₁,h₂,h₃,h₄,h₅,h⟩
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  cases h₅
  rcases h with (⟨h₆,h⟩|⟨h₆,h⟩)
  · rcases h with (h|h)
    · simp [- Bool.toSierraBool_not] at h
      rcases h with ⟨h,(h₁|h₁)⟩
      · rcases h₁ with ⟨h₁,(h₂|h₂)⟩
        · rcases h₂ with ⟨rfl,(h₂|h₂)⟩
          · rw [← decide_not, Bool.toSierraBool_decide_inl', not_not] at h h₁
            rcases h₂ with ⟨h₂,h₃⟩
            cases h₃
            congr 1
            · rw [UInt256.mul_def, UInt256.ofBitVec]
              dsimp
              simp at h₆
              congr 1
              · bv_decide
              · sorry
            · sorry
          · sorry
        · sorry
      · sorry
    · sorry
  · rcases h with (⟨h₇,rfl⟩|h)
    · simp [UInt256.mul_def]
      sorry
    · sorry

aegis_spec "core::integer::u256_checked_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  a.toNat * b.toNat < U256_MOD ∧ ρ = .inl (a * b) ∨
    U256_MOD ≤ a.toNat * b.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::u256_checked_mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold_spec "core::integer::u256_checked_mul"
  aesop

aegis_spec "core::integer::U256Mul::mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  a.toNat * b.toNat < U256_MOD ∧ ρ = .inl (a * b) ∨
    U256_MOD ≤ a.toNat * b.toNat ∧ ρ.isRight

aegis_prove "core::integer::U256Mul::mul" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold_spec "core::integer::U256Mul::mul"
  aesop

aegis_spec "core::integer::U256PartialOrd::lt" :=
  fun _ _ (a b : UInt256) _ ρ =>
  ρ = Bool.toSierraBool ((a.2 ++ a.1) < (b.2 ++ b.1))

aegis_prove "core::integer::U256PartialOrd::lt" :=
  fun _ _ (a b : UInt256) _ ρ => by
  unfold_spec "core::integer::U256PartialOrd::lt"
  rintro ⟨_,_,_,_,_,_,_,_,rfl,rfl,(h|h)⟩
  · rcases h with ⟨h,(h₁|h₁)⟩
    · rcases h₁ with ⟨h₁,rfl⟩
      simp only [Bool.toSierraBool_decide_inl', BitVec.not_lt, Nat.reduceAdd] at h h₁ ⊢
      bv_decide
    · rcases h₁ with ⟨h₁,rfl⟩
      simp only [Bool.toSierraBool_decide_inl', BitVec.not_lt, Bool.toSierraBool_decide_inr',
        Nat.reduceAdd] at h h₁ ⊢
      subst h₁
      congr 1
      bv_decide
  · rcases h with ⟨h,rfl⟩
    simp only [Bool.toSierraBool_decide_inr', Nat.reduceAdd] at h ⊢
    bv_decide

aegis_spec "core::integer::u256_safe_div_rem" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 × UInt256) =>
  ρ.1.2 ++ ρ.1.1 = (a.2 ++ a.1) / (b.2 ++ b.1) ∧
    ρ.2.2 ++ ρ.2.1 = (a.2 ++ a.1) % (b.2 ++ b.1)

aegis_prove "core::integer::u256_safe_div_rem" :=
  fun _ _ (a b : UInt256) _ ρ => by
  unfold_spec "core::integer::u256_safe_div_rem"
  aesop

aegis_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u256>>::expect" :=
  fun _ a err ρ =>
  ρ = a.map id (fun _ => ((), [err]))

aegis_prove "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u256>>::expect" :=
  fun _ a err ρ => by
  unfold_spec "core::option::OptionTraitImpl<core::zeroable::NonZero<core::integer::u256>>::expect"
  aesop

aegis_spec "core::integer::U256DivRem::div_rem" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 × UInt256) =>
  ρ.1.2 ++ ρ.1.1 = (a.2 ++ a.1) / (b.2 ++ b.1) ∧
    ρ.2.2 ++ ρ.2.1 = (a.2 ++ a.1) % (b.2 ++ b.1)

aegis_prove "core::integer::U256DivRem::div_rem" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::U256DivRem::div_rem"
  aesop

aegis_spec "core::integer::by_div_rem::DivImpl::<core::integer::u256, core::integer::U256DivRem, core::integer::U256TryIntoNonZero, core::integer::u256Drop>::div" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) =>
  b ≠ 0 ∧ ρ.isLeft ∧ ρ.getLeft?.get! = .ofBitVec ((a.2 ++ a.1) / (b.2 ++ b.1)) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::DivImpl::<core::integer::u256, core::integer::U256DivRem, core::integer::U256TryIntoNonZero, core::integer::u256Drop>::div" :=
  fun _ _ (a b : UInt256) _ (ρ : UInt256 ⊕ _) => by
  unfold_spec "core::integer::by_div_rem::DivImpl::<core::integer::u256, core::integer::U256DivRem, core::integer::U256TryIntoNonZero, core::integer::u256Drop>::div"
  simp only [UInt256.toNat, UInt256.zero_def]
  rcases b with ⟨bₗ,bₕ⟩; dsimp only
  rintro ⟨_,_,_,_,_,_,(⟨h,rfl⟩|⟨rfl,rfl,h⟩),h'⟩
  · left
    rcases h' with (⟨he,h'⟩|h')
    · injection he with he; cases he
      simp only [Sum.map_inl, id_eq, Sum.inl.injEq, false_and, or_false] at h'
      rcases h' with ⟨_,_,rfl,rfl⟩
      simp at *
      constructor
      · intro he
        simp only [UInt256.ofBitVec, BitVec.extractLsb'_zero] at he
        cases he
        simp at h
      · apply UInt256.ext
        simp_all
    · simp at h'
  · right; aesop

aegis_spec "core::integer::U128IntoU256::into" :=
  fun _ a ρ =>
  ρ = (a, 0)

aegis_prove "core::integer::U128IntoU256::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U256TryIntoU128::try_into" :=
  fun _ (a : UInt256) ρ =>
  a.toNat < U128_MOD ∧ ρ = .inl a.1 ∨
    U128_MOD ≤ a.toNat ∧ ρ = .inr ()

aegis_prove "core::integer::U256TryIntoU128::try_into" :=
  fun _ a ρ => by
  unfold_spec "core::integer::U256TryIntoU128::try_into"
  simp only [Bool.toSierraBool_decide_inl', Bool.toSierraBool_decide_inr']
  aesop (add simp [UInt128, UInt256.pair_toNat, U128_MOD], safe forward [BitVec.isLt])
    (config := { warnOnNonterminal := .false })
  have : w_1.toNat ≠ 0 := BitVec.toNat_injective.ne left
  omega

aegis_spec "core::traits::PartialEqSnap<core::integer::u128, core::integer::U128PartialEq>::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "core::traits::PartialEqSnap<core::integer::u128, core::integer::U128PartialEq>::eq" :=
  fun _ a b ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::u256PartialEq::eq" :=
  fun _ (a b : UInt256) ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "core::integer::u256PartialEq::eq" :=
  fun _ (a b : UInt256) ρ => by
  unfold_spec "core::integer::u256PartialEq::eq"
  rintro ⟨_,_,_,_,_,_,_,_,_,_,rfl,rfl,(h|h)⟩
  · rcases h with ⟨h,rfl⟩
    rw [Bool.toSierraBool_decide_inl'] at h ⊢
    intro h'; injection h'; contradiction
  · rcases h with ⟨h,h₁,h₂,rfl⟩
    rw [Bool.toSierraBool_decide_inr'] at h; cases h
    congr 2
    cases h₁; cases h₂
    apply propext
    constructor
    · rintro rfl; rfl
    · rintro h; cases h; rfl

aegis_spec "core::traits::TIntoT<core::integer::u128>::into" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::traits::TIntoT<core::integer::u128>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::by_div_rem::RemImpl::<core::integer::u8, core::integer::U8DivRem, core::integer::U8TryIntoNonZero, core::integer::u8Drop>::rem" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (BitVec.umod a b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::RemImpl::<core::integer::u8, core::integer::U8DivRem, core::integer::U8TryIntoNonZero, core::integer::u8Drop>::rem" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::RemImpl::<core::integer::u8, core::integer::U8DivRem, core::integer::U8TryIntoNonZero, core::integer::u8Drop>::rem"
  aesop

aegis_spec "core::integer::by_div_rem::RemImpl::<core::integer::u16, core::integer::U16DivRem, core::integer::U16TryIntoNonZero, core::integer::u16Drop>::rem" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (BitVec.umod a b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::RemImpl::<core::integer::u16, core::integer::U16DivRem, core::integer::U16TryIntoNonZero, core::integer::u16Drop>::rem" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::RemImpl::<core::integer::u16, core::integer::U16DivRem, core::integer::U16TryIntoNonZero, core::integer::u16Drop>::rem"
  aesop

aegis_spec "core::integer::by_div_rem::RemImpl::<core::integer::u32, core::integer::U32DivRem, core::integer::U32TryIntoNonZero, core::integer::u32Drop>::rem" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (BitVec.umod a b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::RemImpl::<core::integer::u32, core::integer::U32DivRem, core::integer::U32TryIntoNonZero, core::integer::u32Drop>::rem" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::RemImpl::<core::integer::u32, core::integer::U32DivRem, core::integer::U32TryIntoNonZero, core::integer::u32Drop>::rem"
  aesop

aegis_spec "core::integer::by_div_rem::RemImpl::<core::integer::u64, core::integer::U64DivRem, core::integer::U64TryIntoNonZero, core::integer::u64Drop>::rem" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (BitVec.umod a b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::RemImpl::<core::integer::u64, core::integer::U64DivRem, core::integer::U64TryIntoNonZero, core::integer::u64Drop>::rem" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::RemImpl::<core::integer::u64, core::integer::U64DivRem, core::integer::U64TryIntoNonZero, core::integer::u64Drop>::rem"
  aesop

aegis_spec "core::integer::by_div_rem::RemImpl::<core::integer::u128, core::integer::U128DivRem, core::integer::U128TryIntoNonZero, core::integer::u128Drop>::rem" :=
  fun _ _ a b _ ρ =>
  b ≠ 0 ∧ ρ = .inl (BitVec.umod a b) ∨
    b = 0 ∧ ρ.isRight

aegis_prove "core::integer::by_div_rem::RemImpl::<core::integer::u128, core::integer::U128DivRem, core::integer::U128TryIntoNonZero, core::integer::u128Drop>::rem" :=
  fun _ _ a b _ ρ => by
  unfold_spec "core::integer::by_div_rem::RemImpl::<core::integer::u128, core::integer::U128DivRem, core::integer::U128TryIntoNonZero, core::integer::u128Drop>::rem"
  aesop

aegis_spec "core::integer::U128IntoFelt252::into" :=
  fun _ (a : UInt128) ρ =>
  ρ = a.toFelt

aegis_prove "core::integer::U128IntoFelt252::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::Felt252TryIntoU128::try_into" :=
  fun _ _ a _ ρ =>
  a.val < U128_MOD ∧ ρ = .inl a.cast ∨
    U128_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "core::integer::Felt252TryIntoU128::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::integer::Felt252TryIntoU128::try_into"
  aesop

aegis_spec "core::integer::U64IntoFelt252::into" :=
  fun _ (a : Sierra.UInt64) ρ =>
  ρ = a.toFelt

aegis_prove "core::integer::U64IntoFelt252::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U32IntoFelt252::into" :=
  fun _ (a : Sierra.UInt32) ρ =>
  ρ = a.toFelt

aegis_prove "core::integer::U32IntoFelt252::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::integer::U8IntoFelt252::into" :=
  fun _ a ρ =>
  ρ = a.toFelt

aegis_prove "core::integer::U8IntoFelt252::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::array::ArrayToSpan<core::integer::u128>::span" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::array::ArrayToSpan<core::integer::u128>::span" :=
  fun _ a ρ => by
  rintro rfl
  rfl
