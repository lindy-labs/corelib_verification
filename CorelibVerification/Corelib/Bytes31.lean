import CorelibVerification.Corelib.Integer.Zeroable

aegis_spec "core::array::ArrayImpl<core::bytes_31::bytes31>::new" :=
  fun _ ρ =>
  ρ = []

aegis_prove "core::array::ArrayImpl<core::bytes_31::bytes31>::new" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::array::ArrayDefault<core::bytes_31::bytes31>::default" :=
  fun _ ρ =>
  ρ = []

aegis_prove "core::array::ArrayDefault<core::bytes_31::bytes31>::default" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::bytes_31::Felt252TryIntoBytes31::try_into" :=
  fun _ _ a _ ρ =>
  a.val < 2 ^ 248 ∧ ρ = .inl a.val ∨
    2 ^ 248 ≤ a.val ∧ ρ = .inr ()

aegis_prove "core::bytes_31::Felt252TryIntoBytes31::try_into" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::bytes_31::Felt252TryIntoBytes31::try_into"
  aesop

aegis_spec "core::bytes_31::Bytes31IntoFelt252::into" :=
  fun _ a ρ =>
  ρ = a.toNat

aegis_prove "core::bytes_31::Bytes31IntoFelt252::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::bytes_31::one_shift_left_bytes_u128_nz" :=
  fun _ _ a _ ρ =>
  a < 16 ∧ ρ = .inl (1#128 <<< (8#32 * a)) ∨
    16 ≤ a ∧ ρ.isRight

aegis_prove "core::bytes_31::one_shift_left_bytes_u128_nz" :=
  fun _ _ a _ ρ => by
  intro h
  unfold_spec "core::bytes_31::one_shift_left_bytes_u128_nz"
  by_cases ha₀ : a = 0#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 1#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 2#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 3#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 4#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 5#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 6#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 7#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 8#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 9#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₀ : a = 10#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 11#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 12#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 13#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 14#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  by_cases ha₁ : a = 15#32; left; aesop (add simp [Sierra.UnitEnum.fromIdx])
  have : 16 ≤ a := by bv_decide
  refine .inr ⟨this, ?_⟩
  rw [BitVec.le_def] at this
  simp at this
  rcases h with ⟨_,_,_,_,_,_,_,_,_,__,_,_,_,_,_,_,(⟨-,h₂,-⟩|⟨-,rfl⟩)⟩
  · exfalso
    omega
  · simp

aegis_spec "core::bytes_31::one_shift_left_bytes_u128" :=
  fun _ _ a _ ρ =>
  a < 16 ∧ ρ = .inl (1#128 <<< (8#32 * a)) ∨
    16 ≤ a ∧ ρ.isRight

aegis_prove "core::bytes_31::one_shift_left_bytes_u128" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::bytes_31::one_shift_left_bytes_u128"
  aesop

aegis_spec "core::bytes_31::one_shift_left_bytes_felt252" :=
  fun _ _ a _ ρ =>
  a ≤ 31 ∧ ρ = .inl (1 <<< (8 * a.toNat)) ∨
    31 < a ∧ ρ.isRight

aegis_prove "core::bytes_31::one_shift_left_bytes_felt252" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::bytes_31::one_shift_left_bytes_felt252"
  rintro ⟨_,_,_,_,_,_,_,_,_,_,_,(⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩)⟩
  · rcases h₃ with (⟨h₃,h₄,h₅⟩|⟨rfl,rfl⟩)
    · subst h₃
      rcases h₅ with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
      · simp at h₂
        rcases h₂ with ⟨h₂,rfl⟩
        simp at h₁ ⊢
        have h₁' : 16 ≤ a.toNat := h₁
        simp only [Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false] at h₄
        rcases h₄ with ⟨h₄,rfl⟩
        refine ⟨by bv_decide, ?_⟩
        have alt'' : (a - 16#32).toNat < 16 := by
          erw [← BitVec.lt_def (y := 16#32)]
          exact h₄
        simp only [Sierra.UInt128.toFelt, Nat.reducePow, BitVec.shiftLeft_eq', BitVec.toNat_mul,
          Nat.reduceMod, Nat.reduceSub, Nat.mul_mod_mod,
          BitVec.toFin_shiftLeft, Nat.one_mod, Fin.ofNat'_eq_cast, Fin.castLe_natCast, BitVec.toNat_ofNat]
        have hlt : 1 <<< (8 * BitVec.toNat (a - 16#32)) < 340282366920938463463374607431768211456 := by
          rw [Nat.one_shiftLeft]
          have := Nat.pow_le_pow_of_le (a := 2) (m := 8 * 15) (n := (8 * BitVec.toNat (a - 16#32))) (by simp) (by omega)
          omega
        rw [Nat.mod_eq_of_lt (show 8 * BitVec.toNat (a - 16#32) < 4294967296 by omega), Nat.mod_eq_of_lt hlt]
        erw [← Nat.cast_mul]
        congr 1
        rw [BitVec.toNat_sub_of_le h₁]
        simp [Nat.one_shiftLeft]
        have : 340282366920938463463374607431768211456 = 2 ^ 128 := by rfl
        rw [this, ← Nat.pow_add]
        have : 128 ≤ 8 * BitVec.toNat a := by omega
        simp [Nat.mul_sub, Nat.sub_add_cancel this]
      · simp [BitVec.usubOverflow_eq] at h₁ h₂ h₄ ⊢
        bv_decide
    · simp [BitVec.usubOverflow_eq] at h₁ h₂
      bv_decide
  · rcases h₃ with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · simp at h₂
      rcases h₂ with ⟨h₂,rfl⟩
      left
      simp
      refine ⟨by bv_decide, ?_⟩
      rw [BitVec.lt_def] at h₂
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h₂
      have : 8 * a.toNat % 4294967296 = 8 * a.toNat := by
        rw [Nat.mod_eq_of_lt]
        omega
      simp [this, Sierra.UInt128.toFelt, Fin.castLe_natCast]
      rw [Nat.mod_eq_of_lt]
      have := Nat.pow_le_pow_of_le (a := 2) (m := 8 * 15) (n := 8 * a.toNat) (by simp) (by omega)
      rw [Nat.one_shiftLeft]
      omega
    · simp at h₂ h₁
      bv_decide
