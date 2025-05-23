import CorelibVerification.Aux.Option
import CorelibVerification.Aux.List
import CorelibVerification.Aux.Bool
import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.Integer.Internal
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
            simp_all only [not_lt, Option.filter_decide_false_some, Option.map_none, Option.toSum_none]
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
  fun _ _ _ data str _ _ ρ =>
  ρ = .inl (str ++ data.map UInt64.toFelt, ()) ∨
    ρ.isRight

aegis_prove "core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::serialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  aesop

aegis_spec "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun _ _ _ data str _ _ ρ =>
  ρ = .inl (str ++ data, ()) ∨
    ρ.isRight

set_option grind.warning false

aegis_prove "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::serialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  aesop

aegis_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize" :=
  fun _ _ _ data str _ _ ρ =>
  ρ = .inl (str ++ [(data.length : Sierra.UInt32).toFelt] ++ data, ()) ∨
    ρ.isRight

aegis_prove "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::serialize"
  aesop

aegis_spec "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun _ _ _ s curr r _ _ ρ =>
  (if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U128_MOD) then
      ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map (fun x => .ofNat _ x.val)))
  else ρ = .inl ((s.dropWhileN (·.val < U128_MOD) r.val).tail, .inr ())) ∨
    ρ.isRight

aegis_prove "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold_spec "core::array::deserialize_array_helper::<core::integer::u128, core::serde::into_felt252_based::SerdeImpl::<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  rintro ⟨_,_,_,_,_,(⟨-,h⟩|⟨-,h⟩)⟩
  · rcases h with (⟨h₁,h⟩|h)
    · simp only [Int.cast_zero, Bool.toSierraBool_decide_inl'] at h₁
      rcases h with (⟨h₂,h,rfl⟩|⟨h₂,rfl⟩)
      simp only [Option.inl_eq_toSum_iff, Option.map_eq_some_iff,
        Option.mem_def, decide_eq_true_eq, Function.comp_apply] at h₂
      · rcases h with (h|h)
        · simp only [Int.cast_one, List.length_tail, List.all_eq_true, decide_eq_true_eq,
            List.drop_tail, List.map_take, List.map_tail, List.append_assoc, List.cons_append,
            List.nil_append] at h ⊢
          split_ifs at h with h₃
          · rcases s with (⟨⟩|⟨hd,tl⟩)
            · aesop
            · simp only [List.length_cons, add_tsub_cancel_right, List.tail_cons,
                List.drop_succ_cons, List.map_cons, List.head?_cons, Option.some.injEq, existsAndEq,
                true_and] at *
              rw [ZMod.val_sub_one h₁, Nat.sub_le_iff_le_add] at h₃
              have : r.val ≤ tl.length + 1 ∧ ∀ x ∈ List.take (ZMod.val r) (hd :: tl), ZMod.val x < U128_MOD := by
                refine ⟨h₃.1, fun x hx => ?_⟩
                rw [List.take_cons (ZMod.val_pos.mpr h₁), List.mem_cons] at hx
                rcases hx with (rfl|hx)
                · simp only [Option.filter_eq_some_iff, Option.some.injEq, decide_eq_true_eq,
                    existsAndEq, true_and] at h₂
                  exact h₂.1
                · exact h₃.2 x hx
              split_ifs
              subst h
              left
              congr 2
              · rw [ZMod.val_sub_one h₁, List.drop_cons _ _ (ZMod.val_pos.mpr h₁)]
              · simp only [Option.filter_eq_some_iff, Option.some.injEq, decide_eq_true_eq,
                  existsAndEq, true_and] at h₂
                cases h₂.2
                rw [List.take_cons (ZMod.val_pos.mpr h₁), ZMod.val_sub_one h₁]
          · cases h
            left
            simp only [not_and, not_forall, Classical.not_imp, not_lt, Sum.inl.injEq, Prod.mk.injEq,
              reduceCtorEq, and_false, and_true, if_false_left] at h₃ ⊢
            constructor
            · simp only [ZMod.val_sub_one h₁, tsub_le_iff_right, exists_prop] at h₃
              intro h
              obtain ⟨x, hx, h₃⟩ := h₃ (h.trans (by omega))
              refine ⟨x, ?_, h₃⟩
              rw [List.take_pred_tail (ZMod.val_pos.mpr h₁)] at hx
              exact List.mem_of_mem_tail hx
            · simp only [ZMod.val_sub_one h₁]
              rcases s with (⟨⟩|⟨hd,tl⟩)
              · simp
              · simp at h₂ ⊢
                rw [List.dropWhileN_cons_of_pos _ _ _ (ZMod.val_pos.mpr h₁)]
                simp [h₂.1]
        · aesop
      · simp only [Option.inr_eq_toSum_iff, Option.map_eq_none_iff, Option.filter_eq_none_iff,
          decide_eq_true_eq, not_lt] at h₂
        have hr : ZMod.val r > 0 := ZMod.val_pos.mpr h₁
        rcases s with (⟨⟩|⟨hd,tl⟩)
        · aesop
        · aesop (config := { warnOnNonterminal := .false })
          · use hd
            simp_all [List.take_cons]
          · rw [List.dropWhileN_cons_of_pos _ _ _ hr]
            simp [not_lt_of_ge h₂]
          · use hd
            simp_all [List.take_cons]
          · rw [List.dropWhileN_cons_of_pos _ _ _ hr]
            simp [not_lt_of_ge h₂]
          · use hd
            simp_all [List.take_cons]
          · rw [List.dropWhileN_cons_of_pos _ _ _ hr]
            simp [not_lt_of_ge h₂]
    · aesop
  · aesop

aegis_spec "core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun _ _ _ s curr r _ _ ρ =>
  (if r.val ≤ s.length then
     ρ = .inl (s.drop r.val, .inl (curr ++ s.take r.val))
    else ρ = .inl (s.drop r.val, .inr ())) ∨ ρ.isRight

aegis_prove "core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold_spec "core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>"
  generalize m.costs id!"core::array::deserialize_array_helper::<core::felt252, core::Felt252Serde, core::felt252Drop>" = c
  rintro ⟨_,_,hd,_,_,(⟨hle,h⟩|⟨-,rfl⟩)⟩
  -- Case: Enough gas for one run
  · rcases h with (⟨hne,h⟩|⟨h,rfl,rfl⟩)
    -- Case: `r ≠ 0`
    · simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero, Int.cast_zero,
        Bool.toSierraBool_decide_inl'] at hne
      have hr' : 0 < r.val := by rwa [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
      have hr : (r - 1).val = r.val - 1 := by apply ZMod.val_sub; rwa [ZMod.val_one]
      rcases h with (⟨hs,hrec,h⟩|⟨h,rfl,rfl⟩)
      -- Case: `s ≠ []`, recursive call succeeds (only case in which the context should now depend on the spec)
      · have hs' : 0 < s.length := by rw [List.length_pos_iff]; rintro rfl; simp at hs
        rcases h with ⟨rfl,rfl⟩
        simp only [ge_iff_le, List.length_tail, tsub_le_iff_right, List.append_assoc,
          List.singleton_append, Sum.inl.injEq, Prod.mk.injEq, Sum.isRight_inl,
          Nat.sub_add_cancel hr', Nat.sub_add_cancel hs'] at hrec
        split_ifs at hrec with hrsg
        · rcases hrec with (rfl|hrec)
          · simp [hr, Nat.sub_one_add_one_eq_of_pos hs', Nat.sub_one_add_one_eq_of_pos hr',
              List.take_pred_tail hr'] at hrsg ⊢
            simp [hrsg, Option.inl_eq_toSum_iff] at hs ⊢
            have : hd = s.head (List.ne_nil_of_length_pos hs') := by
              symm
              rwa [← List.head_eq_iff_head?_eq_some] at hs
            rw [this, ← List.head_take (i := r.val) (List.ne_nil_of_length_pos (by rw [List.length_take]; omega))]
            exact List.head_cons_tail (List.take (ZMod.val r) s) _
          · right; assumption
        · rcases hrec with (rfl|hrec)
          · simp [hr, Nat.sub_one_add_one_eq_of_pos hs', Nat.sub_one_add_one_eq_of_pos hr'] at hrsg ⊢
            assumption
          · simp [hrec]
      -- Case: `s = []`
      · have : s = [] := by rwa [Option.inr_eq_toSum_iff, List.head?_eq_none_iff] at h
        simp [this, hne, hle]
    -- Case: `r = 0`
    · simp_all
  -- Case: Not enough gas for one run
  · aesop (add simp [Nat.lt_add_left, add_mul])

aegis_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::deserialize" :=
  fun _ _ _ a _ _ ρ =>
  if h : a = [] then ρ = .inl ([], .inr ())
  else
    let length := (a.head h).val
    let data := a.tail
    (if length ≤ data.length then ρ = .inl (data.drop length, .inl (data.take length))
     else ρ = .inl (data.drop length, .inr ())) ∨
    ρ.isRight

aegis_prove "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold_spec "core::array::ArraySerde::<core::felt252, core::Felt252Serde, core::felt252Drop>::deserialize"
  aesop (add simp [add_mul, List.length_tail])
    (config := { warnOnNonterminal := .false })
  · rwa [List.length_tail, List.head!_eq_head] at left_2
  · rwa [List.length_tail, List.head!_eq_head] at left_2

aegis_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize" :=
  fun _ _ _ data str _ _ ρ =>
  ρ = .inl (str ++ [((data.length : Sierra.UInt32).toFelt : F)] ++ data.map Sierra.UInt64.toFelt, ()) ∨
    ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::serialize"
  aesop

aegis_spec "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun _ _ _ s curr r _ _ ρ =>
  (if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U64_MOD) then
      ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map (fun x => .ofNat _ x.val)))
    else ρ = .inl ((s.dropWhileN (·.val < U64_MOD) r.val).tail, .inr ())) ∨
  ρ.isRight

aegis_prove "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold_spec "core::array::deserialize_array_helper<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>"
  rintro ⟨_,_,_,_,_,(⟨-,h⟩|⟨-,h⟩)⟩
  · rcases h with (⟨h₁,h⟩|h)
    · simp only [Int.cast_zero, Bool.toSierraBool_decide_inl'] at h₁
      rcases h with (⟨h₂,h,rfl⟩|⟨h₂,rfl⟩)
      simp only [Option.inl_eq_toSum_iff, Option.map_eq_some_iff, Option.filter_eq_some_iff,
        Option.mem_def, decide_eq_true_eq, Function.comp_apply] at h₂
      · rcases h with (h|h)
        · simp only [Int.cast_one, List.length_tail, List.all_eq_true, decide_eq_true_eq,
            List.drop_tail, List.map_take, List.map_tail, List.append_assoc, List.cons_append,
            List.nil_append] at h ⊢
          split_ifs at h with h₃
          · rcases s with (⟨⟩|⟨hd,tl⟩)
            · aesop
            · simp only [List.length_cons, add_tsub_cancel_right, List.tail_cons,
                List.drop_succ_cons, List.map_cons, List.head?_cons, Option.some.injEq, existsAndEq,
                true_and] at *
              rw [ZMod.val_sub_one h₁, Nat.sub_le_iff_le_add] at h₃
              have : r.val ≤ tl.length + 1 ∧ ∀ x ∈ List.take (ZMod.val r) (hd :: tl), ZMod.val x < U64_MOD := by
                refine ⟨h₃.1, fun x hx => ?_⟩
                rw [List.take_cons (ZMod.val_pos.mpr h₁), List.mem_cons] at hx
                rcases hx with (rfl|hx)
                · exact h₂.1
                · exact h₃.2 x hx
              split_ifs
              subst h
              left
              congr 2
              · rw [ZMod.val_sub_one h₁, List.drop_cons _ _ (ZMod.val_pos.mpr h₁)]
              · cases h₂.2
                rw [List.take_cons (ZMod.val_pos.mpr h₁), ZMod.val_sub_one h₁]
          · cases h
            left
            simp only [not_and, not_forall, Classical.not_imp, not_lt, Sum.inl.injEq, Prod.mk.injEq,
              reduceCtorEq, and_false, and_true, if_false_left] at h₃ ⊢
            constructor
            · simp only [ZMod.val_sub_one h₁, tsub_le_iff_right, exists_prop] at h₃
              intro h
              obtain ⟨x, hx, h₃⟩ := h₃ (h.trans (by omega))
              refine ⟨x, ?_, h₃⟩
              rw [List.take_pred_tail (ZMod.val_pos.mpr h₁)] at hx
              exact List.mem_of_mem_tail hx
            · simp only [ZMod.val_sub_one h₁]
              rcases s with (⟨⟩|⟨hd,tl⟩)
              · simp
              · simp at h₂ ⊢
                rw [List.dropWhileN_cons_of_pos _ _ _ (ZMod.val_pos.mpr h₁)]
                simp [h₂.1]
        · aesop
      · simp only [Option.inr_eq_toSum_iff, Option.map_eq_none_iff, Option.filter_eq_none_iff,
          decide_eq_true_eq, not_lt] at h₂
        have hr : ZMod.val r > 0 := ZMod.val_pos.mpr h₁
        rcases s with (⟨⟩|⟨hd,tl⟩)
        · aesop
        · aesop (config := { warnOnNonterminal := .false })
          · use hd
            simp_all [List.take_cons]
          · rw [List.dropWhileN_cons_of_pos _ _ _ hr]
            simp [not_lt_of_ge h₂]
          · use hd
            simp_all [List.take_cons]
          · rw [List.dropWhileN_cons_of_pos _ _ _ hr]
            simp [not_lt_of_ge h₂]
          · use hd
            simp_all [List.take_cons]
          · rw [List.dropWhileN_cons_of_pos _ _ _ hr]
            simp [not_lt_of_ge h₂]
    · aesop
  · aesop

aegis_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize" :=
  fun _ _ _ a _ _ ρ =>
  if h : a = [] then ρ = .inl ([], .inr ())
  else
    let length := (a.head h).val
    let data := a.tail
    (if length ≤ data.length ∧ ∀ x ∈ data.take length, ZMod.val x < U64_MOD then
        ρ = .inl (data.drop length, .inl ((data.take length).map (fun x => .ofNat _ x.val)))
      else ρ = .inl ((data.dropWhileN (·.val < U64_MOD) length).tail, .inr ())) ∨
      ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold_spec "core::array::ArraySerde<core::integer::u64, core::serde::into_felt252_based::SerdeImpl<core::integer::u64, core::integer::u64Copy, core::integer::U64IntoFelt252, core::integer::Felt252TryIntoU64>, core::integer::u64Drop>::deserialize"
  rintro ⟨_,_,_,_,_,h₁,h₂⟩
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
  fun _ _ _ data str _ _ ρ =>
  ρ = .inl (str ++ data.map Sierra.UInt128.toFelt, ()) ∨
    ρ.isRight

aegis_prove "core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::serialize_array_helper<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>"
  aesop

aegis_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize" :=
  fun _ _ _ data str _ _ ρ =>
  ρ = .inl (str ++ [(data.length : Sierra.UInt32).toFelt] ++ data.map Sierra.UInt128.toFelt, ()) ∨
    ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::serialize"
  aesop

aegis_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::deserialize" :=
  fun _ _ _ a _ _ ρ =>
  if h : a = [] then ρ = .inl ([], .inr ())
  else
    let length := (a.head h).val
    let data := a.tail
    (if length ≤ data.length ∧ ∀ x ∈ data.take length, ZMod.val x < U128_MOD then
        ρ = .inl (data.drop length, .inl ((data.take length).map ZMod.cast))
      else ρ = .inl ((data.dropWhileN (·.val < U128_MOD) length).tail, .inr ())) ∨
      ρ.isRight

aegis_prove "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold_spec "core::array::ArraySerde<core::integer::u128, core::serde::into_felt252_based::SerdeImpl<core::integer::u128, core::integer::u128Copy, core::integer::U128IntoFelt252, core::integer::Felt252TryIntoU128>, core::integer::u128Drop>::deserialize"
  rintro ⟨_,_,_,_,_,h₁,h₂⟩
  rcases h₁ with (⟨h₁,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
  · rcases a with (_|⟨hda,tla⟩); simp at h₁
    aesop (add simp [add_mul])
  · simp only [reduceCtorEq, List.takeWhileN_nil, List.length_nil, zero_add, one_mul,
      nonpos_iff_eq_zero, ZMod.val_eq_zero, List.take_nil, List.all_nil, and_true, List.drop_nil,
      List.map_nil, List.append_nil, List.dropWhileN_nil, List.tail_nil, false_and, true_and,
      false_or] at h₂
    rcases h₂ with ⟨rfl,rfl,rfl⟩
    simp
