import CorelibVerification.Aux.Option
import CorelibVerification.Aux.List
import CorelibVerification.Aux.Bool
import CorelibVerification.Corelib.Integer
import CorelibVerification.Load
import Mathlib.Data.Option.Basic
--import Lean.Parser.Tactic.Save
import Aegis.Macros

open Sierra

aegis_spec "core::Felt252Serde::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ [a]

aegis_prove "core::Felt252Serde::serialize" :=
  fun _ a b ρ => by
  unfold_spec "core::Felt252Serde::serialize"
  aesop

aegis_spec "core::Felt252Serde::deserialize" :=
  fun _ a ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = a.head?.toSum

aegis_prove "core::Felt252Serde::deserialize" :=
  fun _ a ρ₁ ρ₂ => by
  unfold_spec "core::Felt252Serde::deserialize"
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head])

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ [a.toFelt]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::serialize" :=
  fun _ a b ρ => by
  unfold_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::serialize"
  aesop

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U128_MOD)).map (BitVec.ofNat _ ∘ ZMod.val)).toSum

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>::deserialize"
  aesop (add simp [Option.iget_some], safe tactic (by simp [List.head?_eq_head (by assumption)]))

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ [a.toFelt]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::serialize" :=
  fun _ a b ρ => by
  unfold_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::serialize"
  aesop

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U64_MOD)).map (BitVec.ofNat _ ∘ ZMod.val)).toSum

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>::deserialize"
  aesop (add simp [Option.iget_some], safe tactic (by simp [List.head?_eq_head (by assumption)]))

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ [a.toFelt]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::serialize" :=
  fun _ a b ρ => by
  unfold_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::serialize"
  aesop

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U32_MOD)).map (BitVec.ofNat _ ∘ ZMod.val)).toSum

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u32, core::integer::u32Copy, core::integer::U32IntoFelt252, core::integer::Felt252TryIntoU32>::deserialize"
  aesop (add simp [Option.iget_some], safe tactic (by simp [List.head?_eq_head (by assumption)]))

aegis_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ [a.toFelt]

aegis_prove "core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::serialize" :=
  fun _ a b ρ => by
  unfold_spec "core::serde::into_felt252_based::SerdeImpl::<core::integer::u8, core::integer::u8Copy, core::integer::U8IntoFelt252, core::integer::Felt252TryIntoU8>::serialize"
  aesop

aegis_spec "core::BoolSerde::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ [if (SierraBool.toBool a) then 1 else 0]

aegis_prove "core::BoolSerde::serialize" :=
  fun _ a b ρ _ => by
  unfold_spec "core::BoolSerde::serialize"
  aesop

aegis_spec "core::BoolSerde::deserialize" :=
  fun _ a ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = a.head?.toSum.map (Bool.toSierraBool <| · ≠ 0) id

aegis_prove "core::BoolSerde::deserialize" :=
  fun _ a ρ₁ ρ₂ => by
  unfold_spec "core::BoolSerde::deserialize"
  aesop (add simp [List.head!_eq_head?, List.head?_eq_head, Option.iget_some])

aegis_spec "core::integer::u256Serde::serialize" :=
  fun _ a b ρ =>
  ρ = b ++ ([a.1.toFelt, a.2.toFelt] : List F)

aegis_prove "core::integer::u256Serde::serialize" :=
  fun _ a b ρ => by
  unfold_spec "core::integer::u256Serde::serialize"
  rintro ⟨_,_,_,_,rfl,h,rfl⟩
  injection h with h₁ h₂; subst h₁; subst h₂
  simp

aegis_spec "core::integer::u256Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = (if (a.head?.filter (U128_MOD ≤ ·.val)).isSome then a.tail else a.tail.tail)
  ∧ ρ₂ = ((((a.head?.filter (·.val < U128_MOD))).bind
      (fun ρ₂₁ => (a.tail.head?.filter (·.val < U128_MOD)).map (ρ₂₁, ·))).map
        (Prod.map (BitVec.ofNat _ ∘ ZMod.val) (BitVec.ofNat _ ∘ ZMod.val)) : Option (UInt128 × UInt128)).toSum

aegis_prove "core::integer::u256Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold_spec "core::integer::u256Serde::deserialize"
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
        · aesop
        · simp_all only
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨left_2, right⟩ := right
          subst left_2 right
          split
          · rename_i h
            simp_all only [not_lt, Option.filter_decide_false_some, Option.map_none', Option.toSum_none]
            rw [← left] at left_1
            simp at left_1
          · aesop
      · aesop
  · rcases a with (_|⟨a₁,(_|⟨a₂,as⟩)⟩)
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
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data.map UInt64.toFelt, ())
  else ρ.isRight

aegis_prove "core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  generalize m.costs id!"core::array::serialize_array_helper<core::integer::u64,core::serde::into_felt252_based::SerdeImpl<core::integer::u64,core::integer::u64Copy,core::integer::U64IntoFelt252,core::integer::Felt252TryIntoU64>,core::integer::u64Drop>" = c
  aesop (add simp [add_mul, Nat.sub_mul, Nat.sub_add_eq, tsub_tsub_assoc, Nat.lt_add_left,
      Nat.le_mul_of_pos_left, Nat.sub_add_comm, Nat.sub_lt_iff_lt_add', Nat.le_sub_iff_add_le],
    safe forward [List.length_pos_of_ne], safe [(by grind)])
    (erase simp [List.head_cons_tail])

aegis_spec "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data, ())
  else ρ.isRight

set_option grind.warning false

aegis_prove "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  generalize m.costs id!"core::array::serialize_array_helper<core::felt252,core::Felt252Serde,core::felt252Drop>" = c
  aesop (add simp [add_mul, Nat.sub_mul, Nat.sub_add_eq, tsub_tsub_assoc, Nat.lt_add_left,
      Nat.le_mul_of_pos_left, Nat.sub_add_comm, Nat.sub_lt_iff_lt_add', Nat.le_sub_iff_add_le],
    safe forward [List.length_pos_of_ne]) (config := { warnOnNonterminal := .false })
  · grind

aegis_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::felt252,core::Felt252Serde,core::felt252Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ [(data.length : Sierra.UInt32).toFelt] ++ data, ())
  else ρ.isRight

aegis_prove "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize"
  aesop

aegis_spec "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  if ((s.takeWhileN (·.val < U128_MOD) r.val).length + 1) * c ≤ gas then
    if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U128_MOD) then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map (fun x => .ofNat _ x.val)))
    else ρ = .inl ((s.dropWhileN (·.val < U128_MOD) r.val).tail, .inr ())
  else ρ.isRight

aegis_prove "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold_spec "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  generalize m.costs id!"core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" = c
  rintro ⟨hd,_,_,_,_,_,(⟨hle,h⟩|⟨hlt,rfl⟩)⟩
  · simp only [Int.cast_zero, Bool.toSierraBool_decide_inl', Int.cast_one, List.length_takeWhileN,
      List.length_tail, List.all_eq_true, decide_eq_true_eq, List.drop_tail, List.map_take,
      List.map_tail, List.append_assoc, List.cons_append, List.nil_append,
      Bool.toSierraBool_decide_inr'] at h ⊢
    rcases h with (⟨hnz,h⟩|⟨rfl,rfl,rfl⟩)
    · rcases h with (⟨h,h₁,rfl,rfl⟩|⟨h,rfl,rfl⟩)
      · rw [Option.inl_eq_toSum_iff] at h
        simp at h
        rcases h with ⟨hd, ⟨hhd, hhd'⟩, rfl⟩
        rcases s with (⟨⟩|⟨hd,tl⟩)
        · simp at hhd
        · simp at h₁
          simp at hhd
          subst hhd
          split_ifs at h₁ with h h'
          · rw [ZMod.val_sub_one hnz] at h'
            rcases h₁ with ⟨rfl,rfl⟩
            simp [ZMod.val_sub_one hnz]
            refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
            · rw [List.takeWhile_cons_of_pos (p := fun x => decide (ZMod.val x < U128_MOD)) (decide_eq_true hhd')]
              rw [← Nat.sub_le_sub_iff_right hle]
              refine le_trans ?_ h
              rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz)]
              simp [add_mul, ZMod.val_sub_one hnz]
            · omega
            · rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz), List.take_succ_cons]
              simp [hhd']
              exact h'.2
            · simp [add_mul, Nat.sub_mul, Nat.sub_add_eq]
              rw [Nat.sub_sub_sub_cancel_right (Nat.le_mul_of_pos_left c (ZMod.val_pos.mpr hnz))]
            · conv_rhs => rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz)]
              simp
            · conv_rhs => rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz)]
              rw [List.take_succ_cons]
          · subst h₁
            simp at h'
            simp
            refine ⟨?_, ?_, ?_⟩
            · rw [List.takeWhile_cons_of_pos (p := fun x => decide (ZMod.val x < U128_MOD)) (decide_eq_true hhd'),
                ← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz),
                ← ZMod.val_sub_one hnz]
              simp only [add_mul, one_mul, List.length_cons, Nat.add_min_add_right] at ⊢ h
              rwa [← Nat.le_sub_iff_add_le hle]
            · intro hle2
              rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz),
                ← ZMod.val_sub_one hnz]
              simp [not_le_of_gt hhd']
              apply h'
              rw [ZMod.val_sub_one hnz]
              omega
            · rw [List.dropWhileN_cons_of_pos _ _ _ (ZMod.val_pos.mpr hnz)]
              simp [hhd', ← ZMod.val_sub_one hnz]
          · simp only [List.length_cons, List.map_cons, h₁, if_true_right]
            intro hle2
            exfalso
            rw [List.takeWhile_cons_of_pos (p := fun x => decide (ZMod.val x < U128_MOD)) (decide_eq_true hhd'),
                ← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz),
                ← ZMod.val_sub_one hnz] at hle2
            simp at hle2
            rw [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle] at hle2
            contradiction
      · rw [Option.inr_eq_toSum_iff] at h
        simp only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, and_false, and_true, if_false_left,
          not_and, not_forall, Classical.not_imp, not_lt, Sum.isRight_inl, Bool.false_eq_true,
          if_false_right]
        constructor
        · refine le_trans ?_ hle
          simp only [Option.map_eq_none', Option.filter_eq_none, List.head?_eq_none_iff,
            Option.mem_def, decide_eq_true_eq, not_lt] at h
          cases s
          · simp
          · simp_all [List.takeWhile_cons, not_lt_of_ge]
        · constructor
          · intro hrle
            simp only [Option.map_eq_none', Option.filter_eq_none, List.head?_eq_none_iff,
              Option.mem_def, decide_eq_true_eq, not_lt] at h
            rcases s with (⟨⟩|⟨hd,tl⟩)
            · simp only [List.length_nil, nonpos_iff_eq_zero, ZMod.val_eq_zero] at hrle
              contradiction
            · simp only [reduceCtorEq, List.head?_cons, Option.some.injEq, forall_eq',
                false_or] at h
              use hd
              rw [exists_prop]
              refine ⟨?_, h⟩
              rw [← Nat.sub_one_add_one_eq_of_pos (ZMod.val_pos.mpr hnz)]
              simp
          · rcases s with (⟨⟩|⟨hd,tl⟩)
            · simp
            · simp at h ⊢
              rw [List.dropWhileN_cons_of_pos _ _ _ (ZMod.val_pos.mpr hnz)]
              simp [not_lt_of_ge h]
    · simpa
  · simp only [List.length_takeWhileN, List.all_eq_true, decide_eq_true_eq, Int.cast_ofNat,
      List.nil_append, List.map_take, reduceCtorEq, and_false, ite_self, Sum.isRight_inr,
      if_false_left, not_le, and_true]
    apply lt_of_lt_of_le hlt
    exact Nat.le_mul_of_pos_left c (Nat.zero_lt_succ _)

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
  unfold_spec "core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  generalize m.costs id!"core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" = c
  rintro ⟨_,_,hd,_,_,_,(⟨hle,h⟩|⟨h,rfl⟩)⟩ <;> dsimp only
  -- Case: Enough gas for one run
  · rcases h with (⟨hne,h⟩|⟨h,rfl,rfl⟩)
    -- Case: `r ≠ 0`
    · simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero, Int.cast_zero,
        Bool.toSierraBool_decide_inl'] at hne
      have hr' : 0 < r.val := by rwa [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
      have hr : (r - 1).val = r.val - 1 := by apply ZMod.val_sub; rwa [ZMod.val_one]
      rcases h with (⟨hs,hrec,h⟩|⟨h,rfl,rfl⟩)
      -- Case: `s ≠ []`, recursive call succeeds (only case in which the context should now depend on the spec)
      · dsimp only at hrec;erw [hr] at hrec
        have hs' : 0 < s.length := by rw [List.length_pos_iff]; rintro rfl; simp at hs
        rcases h with ⟨rfl,rfl⟩
        simp only [ge_iff_le, List.length_tail, tsub_le_iff_right, List.append_assoc,
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
            conv_rhs => rw [← Nat.sub_one_add_one_eq_of_pos hr']
            simp
        · rcases hrec with ⟨rfl,rfl⟩
          simpa [hrs, List.drop_tail, Nat.sub_add_cancel hr', prop_if_true_false, add_mul,
            ← Nat.le_sub_iff_add_le hle]
        -- Case: recursive call panics
        · aesop
      -- Case: `s = []`
      · have : s = [] := by rwa [Option.inr_eq_toSum_iff, List.head?_eq_none_iff] at h
        simp [this, hne, hle]
    -- Case: `r = 0`
    · simp_all
  -- Case: Not enough gas for one run
  · aesop (add simp [Nat.lt_add_left, add_mul])

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
  unfold_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::deserialize"
  generalize Metadata.costs m id!"core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" = c
  aesop (add simp [add_mul])
    (config := { warnOnNonterminal := .false })
  · rw [List.head!_eq_head?, List.head?_eq_head left, Option.iget_some] at h
    left; assumption
  · rwa [List.head!_eq_head?, List.head?_eq_head left, Option.iget_some,
      List.length_tail] at left_4
  · rw [List.length_tail] at h_1
    right; assumption
  · rwa [List.head!_eq_head?, List.head?_eq_head left, Option.iget_some,
      List.length_tail] at left_4
  · rw [List.head!_eq_head?, List.head?_eq_head left, Option.iget_some] at h
    left; assumption
  · rwa [List.head!_eq_head?, List.head?_eq_head left, Option.iget_some,
      List.length_tail] at left_4
  · rw [List.length_tail] at h_1
    right; assumption
  · rwa [List.head!_eq_head?, List.head?_eq_head left, Option.iget_some,
      List.length_tail] at left_4
  · rwa [List.head!_eq_head?, List.head?_eq_head left, Option.iget_some] at left_2

aegis_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ [((data.length : Sierra.UInt32).toFelt : F)] ++ data.map Sierra.UInt64.toFelt, ())
  else ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize"
  aesop

aegis_spec "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::array::deserialize_array_helper::<core::integer::u64, core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  if ((s.takeWhileN (·.val < U64_MOD) r.val).length + 1) * c ≤ gas then
    if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U64_MOD) then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map (fun x => .ofNat _ x.val)))
    else ρ = .inl ((s.dropWhileN (·.val < U64_MOD) r.val).tail, .inr ())
  else ρ.isRight

aegis_prove "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold_spec "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  generalize m.costs id!"core::array::deserialize_array_helper::<core::integer::u64, core::serde::into_felt252_based::SerdeImpl::<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" = c
  rintro ⟨hd,_,_,_,_,_,(⟨hle,h⟩|⟨hlt,rfl⟩)⟩
  · simp only [Int.cast_zero, Bool.toSierraBool_decide_inl', Int.cast_one, List.length_takeWhileN,
      List.length_tail, List.all_eq_true, decide_eq_true_eq, List.drop_tail, List.map_take,
      List.map_tail, List.append_assoc, List.cons_append, List.nil_append,
      Bool.toSierraBool_decide_inr'] at h ⊢
    rcases h with (⟨hnz,h⟩|⟨rfl,rfl,rfl⟩)
    · rcases h with (⟨h,h₁,rfl,rfl⟩|⟨h,rfl,rfl⟩)
      · rw [Option.inl_eq_toSum_iff] at h
        simp at h
        rcases h with ⟨hd, ⟨hhd, hhd'⟩, rfl⟩
        rcases s with (⟨⟩|⟨hd,tl⟩)
        · simp at hhd
        · simp at h₁
          simp at hhd
          subst hhd
          split_ifs at h₁ with h h'
          · rw [ZMod.val_sub_one hnz] at h'
            rcases h₁ with ⟨rfl,rfl⟩
            simp [ZMod.val_sub_one hnz]
            refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
            · rw [List.takeWhile_cons_of_pos (p := fun x => decide (ZMod.val x < U64_MOD)) (decide_eq_true hhd')]
              rw [← Nat.sub_le_sub_iff_right hle]
              refine le_trans ?_ h
              rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz)]
              simp [add_mul, ZMod.val_sub_one hnz]
            · omega
            · rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz), List.take_succ_cons]
              simp [hhd']
              exact h'.2
            · simp [add_mul, Nat.sub_mul, Nat.sub_add_eq]
              rw [Nat.sub_sub_sub_cancel_right (Nat.le_mul_of_pos_left c (ZMod.val_pos.mpr hnz))]
            · conv_rhs => rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz)]
              simp
            · conv_rhs => rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz)]
              rw [List.take_succ_cons]
          · subst h₁
            simp at h'
            simp
            refine ⟨?_, ?_, ?_⟩
            · rw [List.takeWhile_cons_of_pos (p := fun x => decide (ZMod.val x < U64_MOD)) (decide_eq_true hhd'),
                ← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz),
                ← ZMod.val_sub_one hnz]
              simp only [add_mul, one_mul, List.length_cons, Nat.add_min_add_right] at ⊢ h
              rwa [← Nat.le_sub_iff_add_le hle]
            · intro hle2
              rw [← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz),
                ← ZMod.val_sub_one hnz]
              simp [not_le_of_gt hhd']
              apply h'
              rw [ZMod.val_sub_one hnz]
              omega
            · rw [List.dropWhileN_cons_of_pos _ _ _ (ZMod.val_pos.mpr hnz)]
              simp [hhd', ← ZMod.val_sub_one hnz]
          · simp only [List.length_cons, List.map_cons, h₁, if_true_right]
            intro hle2
            exfalso
            rw [List.takeWhile_cons_of_pos (p := fun x => decide (ZMod.val x < U64_MOD)) (decide_eq_true hhd'),
                ← Nat.sub_one_add_one ((ZMod.val_ne_zero r).mpr hnz),
                ← ZMod.val_sub_one hnz] at hle2
            simp at hle2
            rw [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle] at hle2
            contradiction
      · rw [Option.inr_eq_toSum_iff] at h
        simp only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, and_false, and_true, if_false_left,
          not_and, not_forall, Classical.not_imp, not_lt, Sum.isRight_inl, Bool.false_eq_true,
          if_false_right]
        constructor
        · refine le_trans ?_ hle
          simp only [Option.map_eq_none', Option.filter_eq_none, List.head?_eq_none_iff,
            Option.mem_def, decide_eq_true_eq, not_lt] at h
          cases s
          · simp
          · simp_all [List.takeWhile_cons, not_lt_of_ge]
        · constructor
          · intro hrle
            simp only [Option.map_eq_none', Option.filter_eq_none, List.head?_eq_none_iff,
              Option.mem_def, decide_eq_true_eq, not_lt] at h
            rcases s with (⟨⟩|⟨hd,tl⟩)
            · simp only [List.length_nil, nonpos_iff_eq_zero, ZMod.val_eq_zero] at hrle
              contradiction
            · simp only [reduceCtorEq, List.head?_cons, Option.some.injEq, forall_eq',
                false_or] at h
              use hd
              rw [exists_prop]
              refine ⟨?_, h⟩
              rw [← Nat.sub_one_add_one_eq_of_pos (ZMod.val_pos.mpr hnz)]
              simp
          · rcases s with (⟨⟩|⟨hd,tl⟩)
            · simp
            · simp at h ⊢
              rw [List.dropWhileN_cons_of_pos _ _ _ (ZMod.val_pos.mpr hnz)]
              simp [not_lt_of_ge h]
    · simpa
  · simp only [List.length_takeWhileN, List.all_eq_true, decide_eq_true_eq, Int.cast_ofNat,
      List.nil_append, List.map_take, reduceCtorEq, and_false, ite_self, Sum.isRight_inr,
      if_false_left, not_le, and_true]
    apply lt_of_lt_of_le hlt
    exact Nat.le_mul_of_pos_left c (Nat.zero_lt_succ _)

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
        ∧ ρ = .inl (data.drop length, .inl ((data.take length).map (fun x => .ofNat _ x.val)))
      else ρ = .inl ((data.dropWhileN (·.val < U64_MOD) length).tail, .inr ())
    else ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize"
  generalize Metadata.costs m id!"core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" = c
  rintro ⟨_,_,_,_,_,_,h₁,h₂⟩
  rcases h₁ with (⟨h₁,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
  · rcases a with (_|⟨hda,tla⟩); simp at h₁
    aesop (add simp [add_mul])
  · simp only [reduceCtorEq, List.takeWhileN_nil, List.length_nil, zero_add, one_mul,
      nonpos_iff_eq_zero, ZMod.val_eq_zero, List.take_nil, List.all_nil, and_true, List.drop_nil,
      List.map_nil, List.append_nil, List.dropWhileN_nil, List.tail_nil, false_and, true_and,
      false_or] at h₂
    rcases h₂ with ⟨rfl,rfl,rfl⟩
    simp

aegis_spec "core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
    if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data.map Sierra.UInt128.toFelt, ())
  else ρ.isRight

aegis_prove "core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  sierra_simp'
  generalize m.costs id!"core::array::serialize_array_helper<core::integer::u128,core::serde::into_felt252_based::SerdeImpl<core::integer::u128,core::integer::u128Copy,core::integer::U128IntoFelt252,core::integer::Felt252TryIntoU128>,core::integer::u128Drop>" = c
  rintro (⟨_,_,hle,h,h'⟩|⟨h,rfl⟩)
  · rw [← List.length_pos_iff] at h
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
  · aesop (add simp [Nat.add_mul], safe apply [Nat.lt_add_left])

aegis_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize" :=
    fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ [(data.length : Sierra.UInt32).toFelt] ++ data.map Sierra.UInt128.toFelt, ())
  else ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize"
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
  unfold_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::deserialize"
  generalize Metadata.costs m id!"core::array::deserialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" = c
  rintro ⟨_,_,_,_,_,_,h₁,h₂⟩
  rcases h₁ with (⟨h₁,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
  · rcases a with (_|⟨hda,tla⟩); simp at h₁
    aesop (add simp [add_mul])
  · simp only [reduceCtorEq, List.takeWhileN_nil, List.length_nil, zero_add, one_mul,
      nonpos_iff_eq_zero, ZMod.val_eq_zero, List.take_nil, List.all_nil, and_true, List.drop_nil,
      List.map_nil, List.append_nil, List.dropWhileN_nil, List.tail_nil, false_and, true_and,
      false_or] at h₂
    rcases h₂ with ⟨rfl,rfl,rfl⟩
    simp
