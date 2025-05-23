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
  · rcases h₃ with (⟨rfl,h₃,h₄⟩|h₃)
    · rcases h₄ with (⟨rfl,rfl⟩|h₄)
      · simp at h₃ h₂ h₁
        rcases h₁ with ⟨h₁,rfl⟩
        rcases h₂ with ⟨h₂,rfl⟩
        rcases h₃ with ⟨h₃,rfl⟩
        simp [BitVec.usubOverflow_eq] at h₁ h₂ h₃ ⊢
        exact ⟨h₁, h₃, rfl⟩
      · right; right; aesop
    · right; left
      dsimp [Sierra.ByteArray.data, Sierra.ByteArray.pendingWord, Sierra.ByteArray.pendingWordLen]
      aesop (config := { warnOnNonterminal := .false, maxSafePrefixRuleApplications := 50 })
      bv_decide
  · right; left; aesop
