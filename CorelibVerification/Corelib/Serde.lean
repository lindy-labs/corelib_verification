import CorelibVerification.Aux.Option
import CorelibVerification.Aux.List
import CorelibVerification.Aux.Bool
import CorelibVerification.Corelib.Integer
import CorelibVerification.Load
import Mathlib.Data.Option.Basic
import Aegis.Macros

open Sierra

aegis_spec "core::serde::Felt252Serde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a]

aegis_prove "core::serde::Felt252Serde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::Felt252Serde::serialize»
  intro
  simp_all only [and_true]

aegis_spec "core::serde::Felt252Serde::deserialize" :=
  fun _ a ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = a.head?.toSum

aegis_prove "core::serde::Felt252Serde::deserialize" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_core::serde::Felt252Serde::deserialize»
  aesop

aegis_spec "core::serde::U128Serde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::U128Serde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::U128Serde::serialize»
  intro
  simp_all only [and_true]

aegis_spec "core::serde::U128Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U128_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::U128Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::U128Serde::deserialize»
  aesop

aegis_spec "core::serde::U64Serde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::U64Serde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::U64Serde::serialize»
  aesop

aegis_spec "core::serde::U64Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U64_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::U64Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::U64Serde::deserialize»
  aesop

aegis_spec "core::serde::U32Serde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::U32Serde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::U32Serde::serialize»
  aesop

aegis_spec "core::serde::U32Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U32_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::U32Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::U32Serde::deserialize»
  aesop

aegis_spec "core::serde::U8Serde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "core::serde::U8Serde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::U8Serde::serialize»
  aesop

aegis_spec "core::serde::U8Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U8_MOD)).map ZMod.cast).toSum

aegis_prove "core::serde::U8Serde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_core::serde::U8Serde::deserialize»
  aesop

aegis_spec "core::serde::BoolSerde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [if (SierraBool.toBool a) then 1 else 0]

aegis_prove "core::serde::BoolSerde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_core::serde::BoolSerde::serialize»
  aesop

aegis_spec "core::serde::BoolSerde::deserialize" :=
  fun _ a ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = a.head?.toSum.map (Bool.toSierraBool <| · ≠ 0) id

aegis_prove "core::serde::BoolSerde::deserialize" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_core::serde::BoolSerde::deserialize»
  aesop

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
    · aesop
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

aegis_spec "core::serde::serialize_array_helper<core::integer::u64, core::serde::U64Serde, core::integer::u64Drop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::serde::serialize_array_helper<core::integer::u64,core::serde::U64Serde,core::integer::u64Drop>"
    if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data.map ZMod.cast, ())
  else ρ.isRight

aegis_prove "core::serde::serialize_array_helper<core::integer::u64, core::serde::U64Serde, core::integer::u64Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::serde::serialize_array_helper<core::integer::u64, core::serde::U64Serde, core::integer::u64Drop>»
  sierra_simp'
  generalize m.costs id!"core::serde::serialize_array_helper<core::integer::u64, core::serde::U64Serde, core::integer::u64Drop>" = c
  rintro (⟨hle,h⟩|⟨h,rfl⟩)
  · rcases h with (⟨a,b,_,d,e,rfl,h₁,h₂,h₃⟩|⟨rfl,rfl,rfl⟩)
    · injection h₁ with h₁; subst h₁
      split_ifs at h₂ with hle'
      · rcases h₂ with ⟨rfl,rfl⟩
        have : (a.length + 2) * c ≤ gas
        · have := Nat.add_le_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.append_assoc, List.singleton_append, Sum.inl.injEq, ge_iff_le,
          tsub_le_iff_right, exists_and_left, exists_and_right, exists_eq_left, Prod.mk.injEq,
          and_true, exists_const, false_and, exists_false, or_false] at h₃
        rcases h₃ with ⟨rfl,rfl⟩
        simp only [List.length_cons, this, ge_iff_le, tsub_le_iff_right, and_true, Sum.isRight_inl,
          ite_true]
        rw [add_mul, one_mul, add_mul, Nat.succ_mul, one_mul, Nat.sub_sub]
        simp only [List.map_cons, and_true]
        ac_rfl
      · have : ¬ (a.length + 2) * c ≤ gas
        · rw [not_le] at hle' ⊢
          have := Nat.add_lt_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.length_cons, this, ge_iff_le, ite_false]
        aesop
    · simp [hle]
  · have : ¬ (data.length + 1) * c ≤ gas
    · rw [not_le, Nat.add_mul, one_mul]; apply Nat.lt_add_left h
    simp [this]

aegis_spec "core::serde::serialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::serde::serialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data, ())
  else ρ.isRight

aegis_prove "core::serde::serialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::serde::serialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>»
  sierra_simp'
  generalize m.costs id!"core::serde::serialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>" = c
  rintro (⟨hle,h⟩|⟨h,rfl⟩)
  · rcases h with (⟨a,b,_,d,e,rfl,h₁,h₂,h₃⟩|⟨rfl,rfl,rfl⟩)
    · injection h₁ with h₁; subst h₁
      split_ifs at h₂ with hle'
      · rcases h₂ with ⟨rfl,rfl⟩
        have : (a.length + 2) * c ≤ gas
        · have := Nat.add_le_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.append_assoc, List.singleton_append, Sum.inl.injEq, ge_iff_le,
          tsub_le_iff_right, exists_and_left, exists_and_right, exists_eq_left, Prod.mk.injEq,
          and_true, exists_const, false_and, exists_false, or_false] at h₃
        rcases h₃ with ⟨rfl,rfl⟩
        simp only [List.length_cons, this, ge_iff_le, tsub_le_iff_right, and_true, Sum.isRight_inl,
          ite_true]
        rw [add_mul, one_mul, add_mul, Nat.succ_mul, one_mul, Nat.sub_sub]
        ac_rfl
      · have : ¬ (a.length + 2) * c ≤ gas
        · rw [not_le] at hle' ⊢
          have := Nat.add_lt_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.length_cons, this, ge_iff_le, ite_false]
        aesop
    · simp [hle]
  · have : ¬ (data.length + 1) * c ≤ gas
    · rw [not_le, Nat.add_mul, one_mul]; apply Nat.lt_add_left h
    simp [this]

attribute [aesop safe forward] Nat.lt_le_antisymm
attribute [simp] add_mul
attribute [aesop safe forward] le_of_add_le_right
attribute [aesop unsafe forward] le_of_add_le_left
erase_aesop_rules [cases Sum]

aegis_spec "core::serde::ArraySerde<core::felt252, core::serde::Felt252Serde, core::felt252Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::serde::serialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>"
  if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ [((data.length : Sierra.UInt32).cast : F)] ++ data, ())
  else ρ.isRight

aegis_prove "core::serde::ArraySerde<core::felt252, core::serde::Felt252Serde, core::felt252Drop>::serialize" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::serde::ArraySerde<core::felt252, core::serde::Felt252Serde, core::felt252Drop>::serialize»
  aesop

aegis_spec "core::serde::deserialize_array_helper<core::integer::u128, core::serde::U128Serde, core::integer::u128Drop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::serde::deserialize_array_helper<core::integer::u128, core::serde::U128Serde, core::integer::u128Drop>"
  if ((s.takeWhileN (·.val < U128_MOD) r.val).length + 1) * c ≤ gas then
    if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U128_MOD) then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map .cast))
    else ρ = .inl ((s.dropWhileN (·.val < U128_MOD) r.val).tail, .inr ())
  else ρ.isRight

aegis_prove "core::serde::deserialize_array_helper<core::integer::u128, core::serde::U128Serde, core::integer::u128Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold «spec_core::serde::deserialize_array_helper<core::integer::u128, core::serde::U128Serde, core::integer::u128Drop>»
  generalize Metadata.costs m id!"core::serde::deserialize_array_helper<core::integer::u128,core::serde::U128Serde,core::integer::u128Drop>" = c
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
            clear hrec  -- TODO seems to be a bug of that the obsolete `hrec` is still in context
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
            · conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr']
          · rcases hrec with ⟨rfl,rfl⟩; clear hrec
            rw [ite_prop_iff_or]; left
            rw [not_and_or] at hrs; rcases hrs with (hrs|hrs)
            · constructor
              · refine le_trans (Nat.mul_le_mul_right _ ?_) hrsg
                simp_all [List.takeWhileN_cons_of_pos]
              · simp only [hrs]
                simp only [List.all_eq_true, decide_eq_true_eq, false_and, ge_iff_le,
                  List.tail_cons, Sum.inl.injEq, Prod.mk.injEq, and_false, and_true, ite_false]
                conv_rhs => rw [List.dropWhileN_cons_of_pos _ _ _ hr', ha]
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
            rw [← Nat.succ_pred_eq_of_pos hr', Nat.min_succ_succ, Nat.succ_mul]
            exact hrec
          · exact ha
      -- Case: recursive call fails due to `s = []` or `s` containing overflows
      · rw [Option.inr_eq_toSum_iff, Option.map_eq_none', Option.filter_eq_none_iff] at h
        rcases h with (h|⟨a,h,h'⟩)
        · rw [@Option.isNone_iff_eq_none, List.head?] at h
          have : s = [] := by aesop
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
  · aesop

aegis_spec "core::serde::deserialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::serde::deserialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>"
  if (r.val + 1) * c ≤ gas ∨ (s.length + 1) * c ≤ gas then
    if r.val ≤ s.length then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ s.take r.val))
    else ρ = .inl (s.drop r.val, .inr ())
  else ρ.isRight  -- TODO investigate why we can't make a statement on `gas'` here

aegis_prove "core::serde::deserialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold «spec_core::serde::deserialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>»
  generalize m.costs id!"core::serde::deserialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>" = c
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
          have h₁ : ¬ ((r.val + 1) * c ≤ gas ∨ (s.length + 1) * c ≤ gas)
          · split_ifs at hrec with h
            simp only [ge_iff_le, Nat.sub_add_cancel hr', Nat.sub_add_cancel hs'] at h
            simpa only [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle]
          simp only [h₁, ge_iff_le, and_false, ite_self, Sum.isRight_inr, ite_false]
      -- Case: `s = []`
      · have : s = [] := by simp only [Option.toSum, Option.elim, List.head?] at h; aesop
        simp [this, hne, hle]
  -- Case: Not enough gas for one run
  · aesop

aegis_spec "core::serde::ArraySerde<core::felt252, core::serde::Felt252Serde, core::felt252Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ =>
  let c := m.costs id!"core::serde::deserialize_array_helper<core::felt252, core::serde::Felt252Serde, core::felt252Drop>"
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

aegis_prove "core::serde::ArraySerde<core::felt252, core::serde::Felt252Serde, core::felt252Drop>::deserialize" :=
  fun m _ gas a _ gas' ρ => by
  unfold «spec_core::serde::ArraySerde<core::felt252, core::serde::Felt252Serde, core::felt252Drop>::deserialize»
  generalize Metadata.costs m id!"core::serde::deserialize_array_helper<core::felt252,core::serde::Felt252Serde,core::felt252Drop>" = c
  sierra_simp'
  aesop