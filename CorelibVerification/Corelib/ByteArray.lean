import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.Bytes31

open Sierra

aegis_spec "core::byte_array::ByteArrayDefault::default" :=
  fun _ ρ =>
  ρ = ([], 0, 0)

aegis_prove "core::byte_array::ByteArrayDefault::default" :=
  fun _ ρ => by
  rintro rfl
  rfl

abbrev Sierra.ByteArray := List Bytes31 × F × Sierra.UInt32

abbrev Sierra.ByteArray.data (x : ByteArray) := x.1

abbrev Sierra.ByteArray.pendingWord (x : ByteArray) := x.2.1

abbrev Sierra.ByteArray.pendingWordLen (x : ByteArray) := x.2.2

def Sierra.ByteArray.setData (x : ByteArray) (d : List Bytes31) : ByteArray :=
  { x with fst := d }

def Sierra.ByteArray.setPendingWord (x : ByteArray) (w : F) : ByteArray :=
  { x with snd := { x.snd with fst := w } }

aegis_spec "core::byte_array::ByteArrayImpl::append_split" :=
  fun _ _ (s : Sierra.ByteArray) c n _ (ρ : Sierra.ByteArray × Unit ⊕ _) =>
  (s.pendingWordLen ≤ 31) ∧
    ((c + s.pendingWord * (1 <<< (8 * (31 - s.pendingWordLen).toNat))).val < 2^248) ∧
    ρ = .inl (⟨s.data ++ [((c + s.pendingWord * (1 <<< (8 * (31 - s.pendingWordLen).toNat))).toNat : Bytes31)],
              n, s.pendingWordLen⟩, ()) ∨
      (31 < s.pendingWordLen) ∧ ρ.isRight ∨
      (2^248 ≤ (c + s.pendingWord * (1 <<< (8 * (31 - s.pendingWordLen).toNat))).toNat) ∧ ρ.isRight

aegis_prove "core::byte_array::ByteArrayImpl::append_split" :=
  fun _ _ (s : Sierra.ByteArray) c n _ (ρ : Sierra.ByteArray × Unit ⊕ _) => by
  unfold_spec "core::byte_array::ByteArrayImpl::append_split"
  rintro ⟨_,_,_,_,_,_,_,_,_,_,_,_,rfl,h₁,(⟨rfl,h₂,h₃⟩|h₂)⟩
  · rcases h₃ with (⟨rfl,h₃,h₄⟩|⟨rfl,rfl⟩)
    · rcases h₄ with (⟨rfl,rfl⟩|h₄)
      · simp only [Nat.reducePow, ZMod.natCast_val, Sum.inl.injEq, reduceCtorEq, and_false,
          or_false, BitVec.ofNat_eq_ofNat, Sum.isRight_inl, Bool.false_eq_true,
          Bool.not_eq_true] at h₃ h₂ h₁
        rcases h₁ with ⟨h₁,rfl⟩
        rcases h₂ with ⟨h₂,rfl⟩
        rcases h₃ with ⟨h₃,rfl⟩
        simp only [BitVec.usubOverflow_eq, decide_eq_false_iff_not, BitVec.not_lt, BitVec.toNat_sub,
          Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, BitVec.ofNat_eq_ofNat, Nat.reduceAdd,
          Fin.toNat_eq_val, BitVec.natCast_eq_ofNat, Sum.inl.injEq, Prod.mk.injEq,
          List.append_cancel_left_eq, List.cons.injEq, and_true, Sum.isRight_inl,
          Bool.false_eq_true, and_false, or_self, or_false] at h₁ h₂ h₃ ⊢
        exact ⟨h₁, h₃, rfl⟩
      · right; right; aesop
    · right; left
      dsimp [Sierra.ByteArray.data, Sierra.ByteArray.pendingWord, Sierra.ByteArray.pendingWordLen]
      simp only [BitVec.ofNat_eq_ofNat, reduceCtorEq, and_false, Sum.isRight_inr, and_true,
        false_or, Bool.not_eq_true, Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true,
        or_false] at h₂ h₁
      rcases h₁ with ⟨h₁,rfl⟩
      refine ⟨?_, rfl⟩
      bv_decide
  · right; left; aesop

aegis_spec "core::byte_array::ByteArrayImpl::append_split_index_gt_16" :=
  fun _ _ (s : Sierra.ByteArray) w si _ (ρ : Sierra.ByteArray × Unit ⊕ _) =>
  let data := UInt128.toFelt (BitVec.extractLsb' 128 128 (w.cast : BitVec 256) / 1#128 <<< (8#32 * (si - 16#32))) + s.pendingWord * (1 <<< (8 * (31 - s.pendingWordLen).toNat))
  let newPending := UInt128.toFelt (BitVec.extractLsb' 128 128 (w.cast : BitVec 256) % 1#128 <<< (8#32 * (si - 16#32))) *
    U128_MOD + UInt128.toFelt (BitVec.extractLsb' 0 128 (w.cast : BitVec 256))
  (16#32 ≤ si) ∧ (si < 32#32) ∧ (data.toNat < 2 ^ 248) ∧
      (s.pendingWordLen ≤ 31#32) ∧
      ρ = .inl ((s.setData (s.data ++ [BitVec.ofNat 248 data.toNat])).setPendingWord newPending, ()) ∨
    (si < 16#32) ∧ ρ.isRight ∨
    (32#32 ≤ si) ∧ ρ.isRight ∨
    (2^248 ≤ data.toNat) ∧ ρ.isRight ∨
    (31#32 < s.pendingWordLen) ∧ ρ.isRight

aegis_prove "core::byte_array::ByteArrayImpl::append_split_index_gt_16" :=
  fun _ _ (s : Sierra.ByteArray) w si _ (ρ : Sierra.ByteArray × Unit ⊕ _) => by
  unfold_spec "core::byte_array::ByteArrayImpl::append_split_index_gt_16"
  rintro ⟨_,_,_,_,_,_,_,_,_,_,h⟩
  rcases h with ⟨_,h₁,h₂,(⟨rfl,h₃,h₄⟩|⟨rfl,rfl⟩)⟩
  · rcases h₄ with (⟨rfl,rfl,h₄,rfl⟩|⟨rfl,rfl⟩)
    · rcases h₄ with (⟨h₄,h₅,rfl⟩|h₄)
      · simp only [UInt256.ofBitVec, ZMod.natCast_val, Prod.mk.injEq, Bool.not_eq_true,
          Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false,
          BitVec.shiftLeft_eq', BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          BitVec.umod_eq, BitVec.udiv_eq, BitVec.ofNat_eq_ofNat, BitVec.toNat_sub] at h₁ h₂ h₃ h₄ h₅
        rcases h₁ with ⟨rfl,rfl⟩
        rcases h₂ with ⟨h₂,rfl⟩
        rcases h₃ with ⟨h₃,rfl,rfl⟩
        left
        simp
        refine ⟨?_, ?_, ?_, h₄, ?_⟩
        · bv_normalize
        · bv_decide
        · simp at h₅ ⊢
          exact h₅
        · simp [ByteArray.setData, ByteArray.setPendingWord, U128_MOD]
      · rcases h₄ with (⟨h₄,h₅⟩|⟨h₄,h₅⟩)
        · simp only [UInt256.ofBitVec, ZMod.natCast_val, Prod.mk.injEq, Bool.not_eq_true,
            Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false,
            BitVec.shiftLeft_eq', BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
            BitVec.umod_eq, BitVec.udiv_eq, BitVec.ofNat_eq_ofNat] at h₁ h₂ h₃ h₄ h₅
          rcases h₁ with ⟨rfl,rfl⟩
          rcases h₂ with ⟨-,rfl⟩
          rcases h₃ with ⟨-,rfl,rfl⟩
          right; right; right; right
          simp only [h₅, and_true, h₄]
        · simp only [UInt256.ofBitVec, ZMod.natCast_val, Prod.mk.injEq, Bool.not_eq_true,
            Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false,
            BitVec.shiftLeft_eq', BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
            BitVec.umod_eq, BitVec.udiv_eq, Nat.reduceAdd, UInt128.toFelt, BitVec.ofNat_eq_ofNat,
            BitVec.toNat_sub, Fin.toNat_eq_val] at h₁ h₂ h₃ h₄ h₅
          rcases h₁ with ⟨rfl,rfl⟩
          rcases h₂ with ⟨-,rfl⟩
          rcases h₃ with ⟨-,rfl,rfl⟩
          right; right; right; left
          generalize BitVec.extractLsb' 128 128 (ZMod.cast w : BitVec 256) = w_high at *
          simp only [BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod,
            Nat.reduceSub, Nat.mul_mod_mod, BitVec.toFin_udiv, BitVec.toFin_shiftLeft, Nat.one_mod,
            Fin.ofNat'_eq_cast, Nat.reduceAdd, BitVec.shiftLeft_eq', BitVec.toNat_mul,
            BitVec.ofNat_eq_ofNat, Fin.toNat_eq_val, h₅, and_true] at h₄ ⊢
          exact h₄
    · simp only [UInt256.ofBitVec, ZMod.natCast_val, Prod.mk.injEq, Bool.not_eq_true,
        Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false, BitVec.shiftLeft_eq',
        BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.umod_eq,
        BitVec.udiv_eq, reduceCtorEq, Sum.isRight_inr, and_true, false_or] at h₁ h₂ h₃
      rcases h₁ with ⟨rfl,rfl⟩
      rcases h₂ with ⟨h₂,rfl⟩
      right; right; left
      simp only [Sum.isRight_inr, and_true]
      bv_decide
  · simp only [UInt256.ofBitVec, ZMod.natCast_val, Prod.mk.injEq, Bool.not_eq_true, reduceCtorEq,
      and_false, Sum.isRight_inr, and_true, false_or] at h₁ h₂
    rcases h₁ with ⟨rfl,rfl⟩
    right; left
    simp only [Sum.isRight_inr, and_true]
    bv_normalize

aegis_spec "core::byte_array::ByteArrayImpl::append_split_index_lt_16" :=
  fun _ _ _ _ _ _ _ => True

aegis_prove "core::byte_array::ByteArrayImpl::append_split_index_lt_16" := sorry

aegis_spec "core::byte_array::ByteArrayImpl::append_split_index_16" :=
  fun _ _ _ _ _ _ => True

aegis_prove "core::byte_array::ByteArrayImpl::append_split_index_16" := sorry

aegis_spec "core::byte_array::ByteArrayImpl::append_word_fits_into_pending" :=
  fun _ _ _ _ _ _ _ => True

aegis_prove "core::byte_array::ByteArrayImpl::append_word_fits_into_pending" := sorry

aegis_spec "core::byte_array::ByteArrayImpl::append_word" :=
  fun _ _ _ _ _ _ _ => True

aegis_prove "core::byte_array::ByteArrayImpl::append_word" := sorry

aegis_spec "core::byte_array::ByteArraySerde::serialize" :=
  fun _ _ _ _ _ _ _ _ => True

aegis_prove "core::byte_array::ByteArraySerde::serialize" := sorry
