import CorelibVerification.Aux.Option
import CorelibVerification.Aux.List
import CorelibVerification.Aux.Bool
import CorelibVerification.Corelib.Integer
import CorelibVerification.Load
import Mathlib.Data.Option.Basic
import Aegis.Macros

open Sierra

aegis_spec "core::Felt252Serde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a]

aegis_prove "core::Felt252Serde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::Felt252Serde::serialize»
  intro
  simp_all only [and_true]

aegis_spec "core::Felt252Serde::deserialize" :=
  fun _ a ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = a.head?.toSum

aegis_prove "core::Felt252Serde::deserialize" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_core::Felt252Serde::deserialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head])

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::serialize»
  intro
  simp_all only [and_true]

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U128_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::deserialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::serialize»
  aesop

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U64_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::deserialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::serialize»
  aesop

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U32_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::deserialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::serialize»
  aesop

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U8_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::deserialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::BoolSerde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [if (SierraBool.toBool a) then 1 else 0]

aegis_prove "core::BoolSerde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::BoolSerde::serialize»
  aesop

aegis_spec "core::BoolSerde::deserialize" :=
  fun _ a ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = a.head?.toSum.map (Bool.toSierraBool <| · ≠ 0) id

aegis_prove "core::BoolSerde::deserialize" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_core::BoolSerde::deserialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::integer::u256Serde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.1.cast, a.2.cast]

aegis_prove "core::integer::u256Serde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::integer::u256Serde::serialize»
  rintro ⟨_,_,_,_,rfl,h,rfl⟩
  injection h with h₁ h₂; subst h₁; subst h₂
  simp

aegis_spec "core::integer::u256Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = (if (a.head?.filter (U128_MOD ≤ ·.val)).isSome then a.tail else a.tail.tail)
  ∧ ρ₂ = ((((a.head?.filter (·.val < U128_MOD))).bind
      (fun ρ₂₁ => (a.tail.head?.filter (·.val < U128_MOD)).map (ρ₂₁, ·))).map
        (Prod.map ZMod.cast ZMod.cast) : Option (UInt128 × UInt128)).toSum

aegis_prove "core::integer::u256Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::integer::u256Serde::deserialize»
  intro h
  constructor
  · rcases a with (_|⟨a₁,(_|⟨a₂,as⟩)⟩)
    · aesop
    · aesop
    · rename_i x x_1 x_2
      simp_all only [List.head?_cons, List.tail_cons, imp_false, Sum.forall, Sum.inl.injEq, not_false_eq_true,
        implies_true, not_true_eq_false, false_implies, and_self, Option.isSome_filter_some, decide_eq_true_eq]
      obtain ⟨w, h⟩ := h
      obtain ⟨w_1, h⟩ := h
      obtain ⟨w_2, h⟩ := h
      obtain ⟨w_3, h⟩ := h
      rcases h with ⟨h_1⟩ | ⟨h_2⟩
      · obtain ⟨left, right⟩ := h_1
        rcases right with ⟨h⟩ | ⟨h_1⟩
        · simp_all only
          obtain ⟨-, right⟩ := h
          obtain ⟨left_2, right⟩ := right
          subst right left_2
          split
          · rename_i h
            simp_all only [not_lt, Option.filter_decide_false_some, Option.map_none', Option.toSum_none]
          · rename_i h
            simp_all only [not_le]
        · simp_all only
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨left_2, right⟩ := right
          subst left_2 right
          split
          · rename_i h
            simp_all only [not_lt, Option.filter_decide_false_some, Option.map_none', Option.toSum_none]
            rw [← left] at left_1
            simp at left_1
          · rename_i h
            simp_all only [not_le]
      · simp_all only
        obtain ⟨left, right⟩ := h_2
        obtain ⟨left_1, right⟩ := right
        subst left_1 right
        split
        · rename_i h
          simp_all only [not_lt, Option.filter_decide_false_some, Option.map_none', Option.toSum_none]
        · rename_i h
          simp_all only [not_le, List.cons_ne_self, Option.filter_decide_true_some, Option.map_some',
            Option.toSum_some]
  · rcases a with (_|⟨a₁,(_|⟨a₂,as⟩)⟩)
    · aesop
    · by_cases hlt : a₁.val < U128_MOD
      · aesop
      · aesop
    · by_cases hlt : a₁.val < U128_MOD
      · by_cases hlt' : a₂.val < U128_MOD
        · simp_all
        · aesop
      · aesop

aegis_spec "core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
    if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data.map ZMod.cast, ())
  else ρ.isRight

aegis_prove "core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>»
  sierra_simp'
  generalize m.costs id!"core::array::serialize_array_helper<core::integer::u64,core::serde::into_felt252_based::SerdeImpl<core::integer::u64,core::integer::u64Copy,core::integer::U64IntoFelt252,core::integer::Felt252TryIntoU64>,core::integer::u64Drop>" = c
  rintro (⟨_,_,hle,h,h'⟩|⟨h,rfl⟩)
  · rw [← List.length_pos] at h
    rcases h with (⟨h,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · rcases h' with (⟨a,b,_,h₁,h₂,h₃⟩|h')
      · cases h₁
        split_ifs at h₂ with hle'
        · rcases h₂ with ⟨rfl,rfl⟩
          have : (data.length + 1) * c ≤ gas := by
            have := Nat.add_le_add_right hle' c
            simp only [Nat.sub_add_cancel hle, List.length_tail, ge_iff_le, Nat.sub_add_cancel h] at this
            linarith
          simp only [List.map_tail, List.append_assoc, List.singleton_append, Sum.inl.injEq,
            ge_iff_le, List.length_tail, tsub_le_iff_right, exists_and_left, exists_and_right,
            exists_eq_left, Prod.mk.injEq, and_true, exists_const, false_and, or_false] at h₃
          rcases h₃ with ⟨rfl,rfl⟩
          simp only [this, ge_iff_le, tsub_le_iff_right, Sum.inl.injEq, Prod.mk.injEq,
            List.append_cancel_left_eq, and_true, Sum.isRight_inl, ite_true, Nat.sub_add_cancel h]
          constructor
          · rw [add_mul, one_mul, add_comm, Nat.sub_sub]
          · cases data
            · simp at h
            · simp
        · have : ¬ (data.length + 1) * c ≤ gas := by
            rw [not_le] at hle' ⊢
            have := Nat.add_lt_add_right hle' c
            simp only [Nat.sub_add_cancel hle, List.length_tail, ge_iff_le, Nat.sub_add_cancel h] at this
            linarith
          simp only [List.length_cons, this, ge_iff_le, ite_false]
          aesop
      · aesop
    · aesop
  · have : ¬ (data.length + 1) * c ≤ gas := by
      rw [not_le, Nat.add_mul, one_mul]; apply Nat.lt_add_left _ h
    simp [this]

aegis_spec "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data, ())
  else ρ.isRight

aegis_prove "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>»
  sierra_simp'
  generalize m.costs id!"core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" = c
  rintro (⟨_,_,hle,h,h'⟩|⟨h,rfl⟩)
  · rw [← List.length_pos] at h
    rcases h with (⟨h,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · rcases h' with (⟨a,b,_,h₁,h₂,h₃⟩|h')
      · cases h₁
        split_ifs at h₂ with hle'
        · rcases h₂ with ⟨rfl,rfl⟩
          have : (data.length + 1) * c ≤ gas := by
            have := Nat.add_le_add_right hle' c
            simp only [Nat.sub_add_cancel hle, List.length_tail, ge_iff_le, Nat.sub_add_cancel h] at this
            linarith
          simp only [List.map_tail, List.append_assoc, List.singleton_append, Sum.inl.injEq,
            ge_iff_le, List.length_tail, tsub_le_iff_right, exists_and_left, exists_and_right,
            exists_eq_left, Prod.mk.injEq, and_true, exists_const, false_and, or_false] at h₃
          rcases h₃ with ⟨rfl,rfl⟩
          simp only [this, ge_iff_le, tsub_le_iff_right, Sum.inl.injEq, Prod.mk.injEq,
            List.append_cancel_left_eq, and_true, Sum.isRight_inl, ite_true, Nat.sub_add_cancel h]
          constructor
          · rw [add_mul, one_mul, add_comm, Nat.sub_sub]
          · cases data
            · simp at h
            · simp
        · have : ¬ (data.length + 1) * c ≤ gas := by
            rw [not_le] at hle' ⊢
            have := Nat.add_lt_add_right hle' c
            simp only [Nat.sub_add_cancel hle, List.length_tail, ge_iff_le, Nat.sub_add_cancel h] at this
            linarith
          simp only [List.length_cons, this, ge_iff_le, ite_false]
          aesop
      · aesop
    · aesop
  · have : ¬ (data.length + 1) * c ≤ gas := by
      rw [not_le, Nat.add_mul, one_mul]; apply Nat.lt_add_left _ h
    simp [this]

attribute [aesop safe forward] Nat.lt_le_asymm
attribute [simp] add_mul
attribute [aesop safe forward] le_of_add_le_right
attribute [aesop unsafe forward] le_of_add_le_left
erase_aesop_rules [cases Sum]

aegis_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::felt252,core::Felt252Serde,core::felt252Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ [((data.length : Sierra.UInt32).cast : F)] ++ data, ())
  else ρ.isRight

aegis_prove "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize»
  aesop

aegis_spec "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  if ((s.takeWhileN (·.val < U128_MOD) r.val).length + 1) * c ≤ gas then
    if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U128_MOD) then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map .cast))
    else ρ = .inl ((s.dropWhileN (·.val < U128_MOD) r.val).tail, .inr ())
  else ρ.isRight

aegis_prove "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold «spec_core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>»
  generalize Metadata.costs m id!"core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" = c
  rintro ⟨hd,_,_,_,_,_,_,_,(⟨hle,h⟩|⟨h,rfl⟩)⟩
  -- Case: Enough gas for one run
  · rcases h with (⟨rfl,rfl,rfl⟩|⟨hne,h⟩)
    -- Case: `r = 0`
    · simp [hle]
    -- Case: `r ≠ 0`
    · have hr' : 0 < r.val := by rwa [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
      have hr : (r - 1).val = r.val - 1 := by apply ZMod.val_sub; rwa [ZMod.val_one]
      rcases h with (⟨hs,hrec,h⟩|⟨h,rfl,rfl⟩)
      -- Case: `s ≠ []`, recursive call succeeds
      · dsimp only at hrec; erw [hr] at hrec
        have hs' : 0 < s.length := by rw [List.length_pos]; rintro rfl; simp at hs
        induction' s with s ss ihs
        · simp at hs'
        clear ihs -- see if we need this
        rw [Option.inl_eq_toSum_iff] at hs
        simp only [List.head?_cons, not_lt, Option.map_eq_some', Option.filter_eq_some_iff] at hs
        rcases hs with ⟨a, ⟨ha, ha'⟩, rfl⟩; rcases ha'
        rcases h with (⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
        -- Case: recursive call does not panic
        · simp only [ge_iff_le, List.length_tail, tsub_le_iff_right, List.append_assoc,
            List.singleton_append, Sum.inl.injEq, Prod.mk.injEq, Sum.isRight_inl,
            Nat.sub_add_cancel hr', Nat.sub_add_cancel hs'] at hrec
          simp only [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle]
          split_ifs at hrec with hrsg hrs
          · rcases hrec with ⟨rfl,rfl,rfl⟩
            --clear hrec  -- TODO seems to be a bug of that the obsolete `hrec` is still in context
            rcases hrs with ⟨hrs,hrs'⟩
            simp only [List.length_cons] at hrs
            simp only [ge_iff_le, List.length_cons, hrs, List.all_eq_true, decide_eq_true_eq,
              true_and, tsub_le_iff_right, Nat.sub_sub, Nat.add_comm c, List.tail_cons, Sum.inl.injEq, Prod.mk.injEq,
              List.append_cancel_left_eq, and_false, ite_prop_iff_or, not_forall, not_lt, exists_prop, or_false,
              Sum.isRight_inl, not_le]
            refine ⟨?_,?_,?_,?_⟩
            · rw [List.tail_cons] at hrs' hrsg
              rw [List.takeWhileN_cons_of_pos _ _ _ hr', ha]
              simp only [ite_true, List.length_cons, ge_iff_le]
              rw [← Nat.add_one]
              exact hrsg
            · intros x hx
              rw [← Nat.succ_pred_eq_of_pos hr', List.take_succ_cons] at hx
              aesop
            · conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr']
              simp
            · conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr']
              simp
          · rcases hrec with ⟨rfl,rfl⟩
            rw [ite_prop_iff_or]; left
            rw [not_and_or] at hrs; rcases hrs with (hrs|hrs)
            · constructor
              · refine le_trans (Nat.mul_le_mul_right _ ?_) hrsg
                simp_all [List.takeWhileN_cons_of_pos]
              · simp only [hrs]
                simp only [List.all_eq_true, decide_eq_true_eq, false_and, ge_iff_le,
                  List.tail_cons, Sum.inl.injEq, Prod.mk.injEq, and_false, and_true, ite_false]
                conv_rhs => rw [List.dropWhileN_cons_of_pos _ _ _ hr', ha]
                simp
            · constructor
              · refine le_trans (Nat.mul_le_mul_right _ ?_) hrsg
                simp_all [List.takeWhileN_cons_of_pos]
              · rw [ite_prop_iff_or]; right; constructor
                · rw [not_and_or]; right
                  contrapose! hrs
                  rw [List.take_pred_tail hr']
                  exact List.all_tail hrs
                · simp_all [List.dropWhileN_cons_of_pos]
        -- Case: recursive call panics
        · rw [List.length_pos] at hs'
          simp only [List.tail_cons, ge_iff_le, List.length_takeWhileN, tsub_le_iff_right, add_mul,
            one_mul, List.all_eq_true, decide_eq_true_eq, List.append_assoc, List.singleton_append,
            and_false, ite_self, Sum.isRight_inr, prop_if_false_true, not_le] at hrec
          simp only [List.length_takeWhileN, ge_iff_le, add_mul, one_mul, List.length_cons,
            List.all_eq_true, decide_eq_true_eq, and_false, ite_self, Sum.isRight_inr,
            prop_if_false_true, not_le, gt_iff_lt]
          rw [List.takeWhile_cons_of_pos]
          · simp only [List.length_cons, ge_iff_le, ← tsub_lt_iff_right hle]
            rw [← Nat.succ_pred_eq_of_pos hr', Nat.succ_min_succ, Nat.succ_mul]
            exact hrec
          · exact ha
      -- Case: recursive call fails due to `s = []` or `s` containing overflows
      · rw [Option.inr_eq_toSum_iff, Option.map_eq_none', Option.filter_eq_none_iff] at h
        rcases h with (h|⟨a,h,h'⟩)
        · rw [@Option.isNone_iff_eq_none, List.head?] at h
          have : s = [] := by cases s <;> simp_all [h]
          subst this
          simp_all
        · rcases s with ⟨_,⟨s,ss⟩⟩
          · simp only [List.head?_nil] at h
          · simp only [List.head?_cons, Option.some.injEq] at h; subst h
            generalize hrval : r.val = rval
            rcases rval with ⟨_,rval⟩
            · simp [hrval] at hr'
            · simp only [decide_eq_true_eq] at h'
              simp [h', hle]
  -- Case: Not enough gas for one run
  · simp only [List.length_takeWhileN, add_mul, one_mul, List.all_eq_true, decide_eq_true_eq,
      Int.ofNat_eq_coe, Nat.cast_ofNat, Int.cast_ofNat, List.nil_append, and_false, ite_self,
      Sum.isRight_inr, if_false_left, not_le, and_true]
    apply Nat.lt_add_left _ h

aegis_spec "core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  if (r.val + 1) * c ≤ gas ∨ (s.length + 1) * c ≤ gas then
    if r.val ≤ s.length then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ s.take r.val))
    else ρ = .inl (s.drop r.val, .inr ())
  else ρ.isRight  -- TODO investigate why we can't make a statement on `gas'` here

aegis_prove "core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold «spec_core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>»
  generalize m.costs id!"core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" = c
  rintro ⟨hd,_,_,_,_,_,_,_,(⟨hle,h⟩|⟨h,rfl⟩)⟩ <;> dsimp only
  -- Case: Enough gas for one run
  · rcases h with (⟨rfl,rfl,rfl⟩|⟨hne,h⟩)
    -- Case: `r = 0`
    · simp_all
    -- Case: `r ≠ 0`
    · have hr' : 0 < r.val := by rwa [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
      have hr : (r - 1).val = r.val - 1 := by apply ZMod.val_sub; rwa [ZMod.val_one]
      rcases h with (⟨hs,hrec,h⟩|⟨h,rfl,rfl⟩)
      -- Case: `s ≠ []`, recursive call succeeds (only case in which the context should now depend on the spec)
      · dsimp only at hrec;erw [hr] at hrec
        have hs' : 0 < s.length := by rw [List.length_pos]; rintro rfl; simp at hs
        rcases h with (⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
        -- Case: recursive call does not panic
        · simp only [ge_iff_le, List.length_tail, tsub_le_iff_right, List.append_assoc,
            List.singleton_append, Sum.inl.injEq, Prod.mk.injEq, Sum.isRight_inl,
            Nat.sub_add_cancel hr', Nat.sub_add_cancel hs'] at hrec
          simp only [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle]
          split_ifs at hrec with hrsg hrs
          · rcases hrec with ⟨rfl,rfl,rfl⟩
            rcases hrsg with (hrsg|hrsg) <;>
            · have : hd ∈ s.head? := by rw [Option.inl_eq_toSum_iff] at hs; simp [hs]
              simp_all only [ne_eq, ge_iff_le, Option.mem_def, true_or, or_true, tsub_le_iff_right,
                Nat.sub_sub, add_comm c, List.drop_tail, Nat.sub_add_cancel hr', Sum.inl.injEq,
                Prod.mk.injEq, List.append_cancel_left_eq, true_and, and_self, ite_true,
                Sum.isRight_inl, Option.toSum_some]
              rw [← List.cons_head?_tail this]
              rw [List.tail_cons, ← @List.take_cons, Nat.sub_one, Nat.succ_pred_eq_of_pos hr']
          · rcases hrec with ⟨rfl,rfl⟩
            simpa [hrs, List.drop_tail, Nat.sub_add_cancel hr', prop_if_true_false, add_mul,
              ← Nat.le_sub_iff_add_le hle]
        -- Case: recursive call panics
        · simp only [ge_iff_le, List.length_tail, tsub_le_iff_right, List.append_assoc,
            List.singleton_append, and_false, ite_self, Sum.isRight_inr] at hrec
          have h₁ : ¬ ((r.val + 1) * c ≤ gas ∨ (s.length + 1) * c ≤ gas) := by
            split_ifs at hrec with h
            simp only [ge_iff_le, Nat.sub_add_cancel hr', Nat.sub_add_cancel hs'] at h
            simpa only [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle]
          simp only [h₁, ge_iff_le, and_false, ite_self, Sum.isRight_inr, ite_false]
      -- Case: `s = []`
      · have : s = [] := by rwa [Option.inr_eq_toSum_iff, List.head?_eq_none_iff] at h
        simp [this, hne, hle]
  -- Case: Not enough gas for one run
  · aesop (add simp [Nat.lt_add_left])

aegis_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  if h : a = [] then ρ = .inl ([], .inr ())
  else
    let length := (a.head h).val
    let data := a.tail
    if (length + 1) * c ≤ gas ∨ (data.length + 1) * c ≤ gas then
      if length ≤ data.length then
        gas' = gas - (length + 1) * c
        ∧ ρ = .inl (data.drop length, .inl (data.take length))
      else ρ = .inl (data.drop length, .inr ())
    else ρ.isRight

aegis_prove "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold «spec_core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::deserialize»
  generalize Metadata.costs m id!"core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" = c
  sierra_simp'
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ [((data.length : Sierra.UInt32).cast : F)] ++ data.map ZMod.cast, ())
  else ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::integer::u64, core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  if ((s.takeWhileN (·.val < U64_MOD) r.val).length + 1) * c ≤ gas then
    if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U64_MOD) then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map .cast))
    else ρ = .inl ((s.dropWhileN (·.val < U64_MOD) r.val).tail, .inr ())
  else ρ.isRight

aegis_prove "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold «spec_core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>»
  generalize m.costs id!"core::array::deserialize_array_helper::<core::integer::u64, core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" = c
  rintro ⟨hd,_,_,_,_,_,_,_,(⟨hle,h⟩|⟨h,rfl⟩)⟩
  -- Case: Enough gas for one run
  · rcases h with (⟨rfl,rfl,rfl⟩|⟨hne,h⟩)
    -- Case: `r = 0`
    · simp [hle]
    -- Case: `r ≠ 0`
    · have hr' : 0 < r.val := by rwa [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
      have hr : (r - 1).val = r.val - 1 := by apply ZMod.val_sub; rwa [ZMod.val_one]
      rcases h with (⟨hs,hrec,h⟩|⟨h,rfl,rfl⟩)
      -- Case: `s ≠ []`, recursive call succeeds
      · dsimp only at hrec; erw [hr] at hrec
        have hs' : 0 < s.length := by rw [List.length_pos]; rintro rfl; simp at hs
        induction' s with s ss ihs
        · simp at hs'
        clear ihs -- see if we need this
        rw [Option.inl_eq_toSum_iff] at hs
        simp only [List.head?_cons, not_lt, Option.map_eq_some', Option.filter_eq_some_iff] at hs
        rcases hs with ⟨a, ⟨ha, ha'⟩, rfl⟩; rcases ha'
        rcases h with (⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
        -- Case: recursive call does not panic
        · simp only [ge_iff_le, List.length_tail, tsub_le_iff_right, List.append_assoc,
            List.singleton_append, Sum.inl.injEq, Prod.mk.injEq, Sum.isRight_inl,
            Nat.sub_add_cancel hr', Nat.sub_add_cancel hs'] at hrec
          simp only [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle]
          split_ifs at hrec with hrsg hrs
          · rcases hrec with ⟨rfl,rfl,rfl⟩
            --clear hrec  -- TODO seems to be a bug of that the obsolete `hrec` is still in context
            rcases hrs with ⟨hrs,hrs'⟩
            simp only [List.length_cons] at hrs
            simp only [ge_iff_le, List.length_cons, hrs, List.all_eq_true, decide_eq_true_eq,
              true_and, tsub_le_iff_right, Nat.sub_sub, Nat.add_comm c, List.tail_cons, Sum.inl.injEq, Prod.mk.injEq,
              List.append_cancel_left_eq, and_false, ite_prop_iff_or, not_forall, not_lt, exists_prop, or_false,
              Sum.isRight_inl, not_le]
            refine ⟨?_,?_,?_,?_⟩
            · rw [List.tail_cons] at hrs' hrsg
              rw [List.takeWhileN_cons_of_pos _ _ _ hr', ha]
              simp only [ite_true, List.length_cons, ge_iff_le]
              rw [← Nat.add_one]
              exact hrsg
            · intros x hx
              rw [← Nat.succ_pred_eq_of_pos hr', List.take_succ_cons] at hx
              aesop
            · conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr']
              simp
            · conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr']
              simp
          · rcases hrec with ⟨rfl,rfl⟩
            rw [ite_prop_iff_or]; left
            rw [not_and_or] at hrs; rcases hrs with (hrs|hrs)
            · constructor
              · refine le_trans (Nat.mul_le_mul_right _ ?_) hrsg
                simp_all [List.takeWhileN_cons_of_pos]
              · simp only [hrs]
                simp only [List.all_eq_true, decide_eq_true_eq, false_and, ge_iff_le,
                  List.tail_cons, Sum.inl.injEq, Prod.mk.injEq, and_false, and_true, ite_false]
                conv_rhs => rw [List.dropWhileN_cons_of_pos _ _ _ hr', ha]
                simp
            · constructor
              · refine le_trans (Nat.mul_le_mul_right _ ?_) hrsg
                simp_all [List.takeWhileN_cons_of_pos]
              · rw [ite_prop_iff_or]; right; constructor
                · rw [not_and_or]; right
                  contrapose! hrs
                  rw [List.take_pred_tail hr']
                  exact List.all_tail hrs
                · simp_all [List.dropWhileN_cons_of_pos]
        -- Case: recursive call panics
        · rw [List.length_pos] at hs'
          simp only [List.tail_cons, ge_iff_le, List.length_takeWhileN, tsub_le_iff_right, add_mul,
            one_mul, List.all_eq_true, decide_eq_true_eq, List.append_assoc, List.singleton_append,
            and_false, ite_self, Sum.isRight_inr, prop_if_false_true, not_le] at hrec
          simp only [List.length_takeWhileN, ge_iff_le, add_mul, one_mul, List.length_cons,
            List.all_eq_true, decide_eq_true_eq, and_false, ite_self, Sum.isRight_inr,
            prop_if_false_true, not_le, gt_iff_lt]
          rw [List.takeWhile_cons_of_pos]
          · simp only [List.length_cons, ge_iff_le, ← tsub_lt_iff_right hle]
            rw [← Nat.succ_pred_eq_of_pos hr', Nat.succ_min_succ, Nat.succ_mul]
            exact hrec
          · exact ha
      -- Case: recursive call fails due to `s = []` or `s` containing overflows
      · rw [Option.inr_eq_toSum_iff, Option.map_eq_none', Option.filter_eq_none_iff] at h
        rcases h with (h|⟨a,h,h'⟩)
        · rw [@Option.isNone_iff_eq_none, List.head?] at h
          have : s = [] := by cases s <;> simp_all [h]
          subst this
          simp_all
        · rcases s with ⟨_,⟨s,ss⟩⟩
          · simp only [List.head?_nil] at h
          · simp only [List.head?_cons, Option.some.injEq] at h; subst h
            generalize hrval : r.val = rval
            rcases rval with ⟨_,rval⟩
            · simp [hrval] at hr'
            · simp only [decide_eq_true_eq] at h'
              simp [h', hle]
  -- Case: Not enough gas for one run
  · aesop (add simp [Nat.lt_add_left])

aegis_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::integer::u64, core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  if h : a = [] then ρ = .inl ([], .inr ())
  else
    let length := (a.head h).val
    let data := a.tail
    if min length (data.takeWhile (·.val < U64_MOD)).length * c + c ≤ gas then
      if length ≤ data.length ∧ ∀ x ∈ data.take length, ZMod.val x < U64_MOD then
        gas' = gas - (length + 1) * c
        ∧ ρ = .inl (data.drop length, .inl ((data.take length).map ZMod.cast))
      else ρ = .inl ((data.dropWhileN (·.val < U64_MOD) length).tail, .inr ())
    else ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold «spec_core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize»
  generalize Metadata.costs m id!"core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" = c
  rintro ⟨_,_,_,_,_,_,_,_,_,_,h₁,h₂⟩
  rcases h₁ with (⟨h₁,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
  · rcases a with (_|⟨hda,tla⟩); simp at h₁
    simp only [ne_eq, not_false_eq_true, List.head!_cons, Sum.inl.injEq, List.tail_cons,
      List.length_takeWhileN, ge_iff_le, add_mul, one_mul, List.all_eq_true, decide_eq_true_eq,
      List.nil_append, false_and, or_false, List.head_cons, dite_eq_ite, ite_false] at *
    rcases h₂ with ⟨rfl,h₂,h₃⟩
    rcases h₃ with (⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · exact h₂
    · exact h₂
  · simp only [List.takeWhileN_nil, List.length_nil, zero_add, one_mul, nonpos_iff_eq_zero,
      ZMod.val_eq_zero, List.take_nil, List.all_nil, and_true, add_mul, ge_iff_le, List.drop_nil,
      List.map_nil, List.append_nil, List.dropWhileN_nil, List.tail_nil, false_and, true_and,
      false_or] at h₂
    rcases h₂ with ⟨rfl,rfl,rfl⟩
    simp

aegis_spec "core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
    if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data.map ZMod.cast, ())
  else ρ.isRight

aegis_prove "core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>»
  sierra_simp'
  generalize m.costs id!"core::array::serialize_array_helper<core::integer::u128,core::serde::into_felt252_based::SerdeImpl<core::integer::u128,core::integer::u128Copy,core::integer::U128IntoFelt252,core::integer::Felt252TryIntoU128>,core::integer::u128Drop>" = c
  rintro (⟨_,_,hle,h,h'⟩|⟨h,rfl⟩)
  · rw [← List.length_pos] at h
    rcases h with (⟨h,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · rcases h' with (⟨a,b,_,h₁,h₂,h₃⟩|h')
      · cases h₁
        split_ifs at h₂ with hle'
        · rcases h₂ with ⟨rfl,rfl⟩
          have : (data.length + 1) * c ≤ gas := by
            have := Nat.add_le_add_right hle' c
            simp only [Nat.sub_add_cancel hle, List.length_tail, ge_iff_le, Nat.sub_add_cancel h] at this
            linarith
          simp only [List.map_tail, List.append_assoc, List.singleton_append, Sum.inl.injEq,
            ge_iff_le, List.length_tail, tsub_le_iff_right, exists_and_left, exists_and_right,
            exists_eq_left, Prod.mk.injEq, and_true, exists_const, false_and, or_false] at h₃
          rcases h₃ with ⟨rfl,rfl⟩
          simp only [this, ge_iff_le, tsub_le_iff_right, Sum.inl.injEq, Prod.mk.injEq,
            List.append_cancel_left_eq, and_true, Sum.isRight_inl, ite_true, Nat.sub_add_cancel h]
          constructor
          · rw [add_mul, one_mul, add_comm, Nat.sub_sub]
          · cases data
            · simp at h
            · simp
        · have : ¬ (data.length + 1) * c ≤ gas := by
            rw [not_le] at hle' ⊢
            have := Nat.add_lt_add_right hle' c
            simp only [Nat.sub_add_cancel hle, List.length_tail, ge_iff_le, Nat.sub_add_cancel h] at this
            linarith
          simp only [List.length_cons, this, ge_iff_le, ite_false]
          aesop
      · aesop
    · aesop
  · aesop (add safe apply [Nat.lt_add_left])

aegis_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize" :=
    fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ [((data.length : Sierra.UInt32).cast : F)] ++ data.map ZMod.cast, ())
  else ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize»
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  if h : a = [] then ρ = .inl ([], .inr ())
  else
    let length := (a.head h).val
    let data := a.tail
    if min length (data.takeWhile (·.val < U128_MOD)).length * c + c ≤ gas then
      if length ≤ data.length ∧ ∀ x ∈ data.take length, ZMod.val x < U128_MOD then
        gas' = gas - (length + 1) * c
        ∧ ρ = .inl (data.drop length, .inl ((data.take length).map ZMod.cast))
      else ρ = .inl ((data.dropWhileN (·.val < U128_MOD) length).tail, .inr ())
    else ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold «spec_core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::deserialize»
  generalize Metadata.costs m id!"core::array::deserialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" = c
  rintro ⟨_,_,_,_,_,_,_,_,_,_,h₁,h₂⟩
  rcases h₁ with (⟨h₁,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
  · rcases a with (_|⟨hda,tla⟩); simp at h₁
    simp only [ne_eq, not_false_eq_true, List.head!_cons, Sum.inl.injEq, List.tail_cons,
      List.length_takeWhileN, ge_iff_le, add_mul, one_mul, List.all_eq_true, decide_eq_true_eq,
      List.nil_append, false_and, or_false, List.head_cons, dite_eq_ite, ite_false] at *
    rcases h₂ with ⟨rfl,h₂,h₃⟩
    rcases h₃ with (⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
    · exact h₂
    · exact h₂
  · simp only [List.takeWhileN_nil, List.length_nil, zero_add, one_mul, nonpos_iff_eq_zero,
      ZMod.val_eq_zero, List.take_nil, List.all_nil, and_true, add_mul, ge_iff_le, List.drop_nil,
      List.map_nil, List.append_nil, List.dropWhileN_nil, List.tail_nil, false_and, true_and,
      false_or] at h₂
    rcases h₂ with ⟨rfl,rfl,rfl⟩
    simp
