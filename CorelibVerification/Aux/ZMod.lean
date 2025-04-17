import Aegis.Types
import Aegis.Aux.ZMod.HMul
import Mathlib.Tactic.NormNum

open Sierra

instance : NeZero PRIME := ⟨by unfold PRIME; norm_num⟩

theorem ZMod.val_pos_of_ne_zero {a : ZMod n} [Fact (1 < n)] (h : a ≠ 0) : 0 < a.val := by
  apply Nat.pos_of_ne_zero
  intro h
  rw [ZMod.val_eq_zero] at h
  contradiction


instance : Fact (1 < U8_MOD) := ⟨by unfold U8_MOD; norm_num⟩

instance : Fact (1 < U128_MOD) := ⟨by unfold U128_MOD; norm_num⟩

instance : NeZero PRIME := ⟨by unfold PRIME; norm_num⟩

instance : Fact (1 < PRIME) := ⟨by unfold PRIME; norm_num⟩

instance : NeZero CONTRACT_ADDRESS_MOD := ⟨by unfold CONTRACT_ADDRESS_MOD; norm_num⟩

instance : Fact (CONTRACT_ADDRESS_MOD < PRIME) := ⟨by norm_num [CONTRACT_ADDRESS_MOD, PRIME]⟩

theorem ZMod.val_add_of_ge {n : ℕ} [NeZero n] {a b : ZMod n} (h : a.val + b.val ≥ n) :
    (a + b).val + n = a.val + b.val := by
  rw [ZMod.val_add, Nat.add_mod_add_of_le_add_mod, Nat.mod_eq_of_lt (ZMod.val_lt _),
    Nat.mod_eq_of_lt (ZMod.val_lt _)]
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)]

theorem ZMod.cast_rat_eq_zero_iff {m : ℕ} [NeZero m] (a : ZMod m) :
    (a.cast : ℚ) = 0 ↔ a = 0 := by
  cases m; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  simp only [ZMod.cast, ZMod.val, Nat.cast_eq_zero]
  constructor
  · aesop
  · intro h; injection h

theorem ZMod.cast_ZMod_eq_zero_iff_of_lt {m n : ℕ} [NeZero m] (h : m < n) (a : ZMod m) :
    (a.cast : ZMod n) = 0 ↔ a = 0 := by
  constructor
  · intro e
    rw [ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at e
    have := a.val_lt
    by_cases hz : val a = 0
    · rwa [← ZMod.val_eq_zero]
    · exfalso
      apply Nat.lt_asymm (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) e) a.val_lt) h
  · intro h; cases h; simp

theorem ZMod.cast_ZMod_ne_zero_iff_of_lt {m n : ℕ} [NeZero m] (h : m < n) (a : ZMod m) :
    (a.cast : ZMod n) ≠ 0 ↔ a ≠ 0 := by
  rw [not_iff_not]
  apply ZMod.cast_ZMod_eq_zero_iff_of_lt h

theorem Nat.mod_eq_of_le_of_lt {a b : ℕ} (h' : b ≤ a) (h'' : a < 2 * b) : a % b = a - b := by
  rw [two_mul] at h''
  symm; apply Nat.sub_eq_of_eq_add
  rw [mod_eq_sub_mod h', mod_eq_of_lt (by apply Nat.sub_lt_left_of_lt_add h' h'')]
  symm; apply Nat.sub_add_cancel h'

theorem Nat.lt_of_add_lt {a b c : ℕ} (h : a + b < c) : a < c :=
  Nat.lt_of_add_lt_add_right (lt_of_lt_of_le h (le_add_right c b))

theorem Nat.le_add_of_le_left {a b c : ℕ} (h : a ≤ b) : a ≤ b + c :=
  Nat.add_le_add h (Nat.zero_le c)

theorem Nat.le_add_of_le_right {a b c : ℕ} (h : a ≤ c) : a ≤ b + c := by
  rw [add_comm]
  apply Nat.le_add_of_le_left h

theorem Nat.mul_add_div_eq_of_lt {a b c : ℕ} (h : c < b) : (b * a + c) / b = a := by
  rw [Nat.add_div_of_dvd_right (Exists.intro a rfl), Nat.div_eq_of_lt h]
  simp
  apply Nat.mul_div_cancel_left
  exact zero_lt_of_lt h

theorem ZMod.hmul_eq_zero_iff {n : ℕ} [NeZero n] (a b : ZMod n) :
    (ZMod.hmul a b = 0) ↔ (a.val * b.val < n) := by
  cases n
  · simp_all only [Nat.zero_eq, neZero_zero_iff_false]
  · constructor
    · simp only [hmul]
      intro h
      injection h with h
      simp only [Nat.zero_mod, add_pos_iff, or_true, Nat.div_eq_zero_iff] at h
      simp only [Nat.add_eq_zero, one_ne_zero, and_false, Nat.succ_eq_add_one, false_or] at h
      exact h
    · intro h
      simp only [hmul]
      apply Fin.ext
      rw [Fin.val_zero]
      simp [Nat.div_eq_zero_iff, h]

theorem ZMod.hmul_eq_zero_iff' {n : ℕ} [NeZero n] (a b : ZMod n) :
    (ZMod.hmul a b = 0) ↔ ((a * b).val = a.val * b.val) :=
  by rw [ZMod.hmul_eq_zero_iff, ZMod.val_mul_iff_lt]

theorem ZMod.hmul_ne_zero_iff {n : ℕ} [NeZero n] (a b : ZMod n) :
    (ZMod.hmul a b ≠ 0) ↔ (n ≤ a.val * b.val) := by
  rw [← not_lt, not_iff_not]
  apply ZMod.hmul_eq_zero_iff

theorem ZMod.val_hmul {n : ℕ} [NeZero n] (a b : ZMod n) :
    (ZMod.hmul a b).val = a.val * b.val / n := by
  cases n
  · simp_all only [Nat.zero_eq, neZero_zero_iff_false]
  · simp only [ZMod.hmul, ZMod.val]

theorem ZMod.val_mul_val_eq_hmul {n : ℕ} [NeZero n] (a b : ZMod n) :
    a.val * b.val = n * (hmul a b).val + (a * b).val := by
  cases n; cases NeZero.ne 0 rfl
  rw [val_mul, val_hmul]
  symm
  apply Nat.div_add_mod (a.val * b.val)

theorem Nat.eq_zero_of_mul_lt_left {a b : ℕ} (h : b * a < a) : b = 0 := by
  rw [← not_le] at h
  by_contra
  apply h
  apply Nat.le_mul_of_pos_left
  apply Nat.pos_of_ne_zero
  assumption

theorem Nat.eq_zero_of_mul_lt_right {a b : ℕ} (h : a * b < a) : b = 0 := by
  rw [mul_comm] at h; apply Nat.eq_zero_of_mul_lt_left h

theorem ZMod.cast_mul_of_val_lt [Ring R] [NeZero n] {a b : ZMod n} (h : a.val * b.val < n) :
    (a.cast : R) * (b.cast : R) = (a * b).cast := by
  rcases n with (⟨⟩|⟨n⟩); · cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp only [cast, val, Fin.val_mk] at *
  rw [Fin.val_mk (n := n + 1) (by simp), Fin.mul_def]
  simp [Nat.mod_eq_of_lt h]

@[simp]
theorem ZMod.cast_cast_of_lt {m n : ℕ} [NeZero m] (h : m < n) {a : ZMod m} :
    ((a.cast : ZMod n).cast : ZMod m) = a := by
  rcases m with (⟨⟩|⟨m⟩); · cases NeZero.ne 0 rfl
  rcases n with (⟨⟩|⟨n⟩); · simp at h
  rcases a with ⟨a, ha⟩
  simp only [cast, Nat.cast, NatCast.natCast, Fin.ofNat', val]
  apply Fin.ext
  dsimp only
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) ha), Nat.mod_eq_of_lt (lt_trans ha h)]

@[simp]
theorem ZMod.castLE_eq_zero_iff_eq_zero {m n : ℕ} (a : ZMod m.succ) (h : m.succ ≤ n) :
    Fin.castLE h a = (@OfNat.ofNat (Fin n) 0 (@Fin.instOfNat _ ⟨by omega⟩ _)) ↔ a = 0 := by
  cases n using Nat.rec
  case zero => simp at h
  case succ n _ =>
    constructor
    · intro h'
      rwa [← Fin.castLE_zero h, Fin.castLE_inj] at h'
    · rintro rfl
      simp

@[simp]
theorem ZMod.val_sub_one {m : ℕ} [NeZero m] [Fact (1 < m)] {a : ZMod m} (h : a ≠ 0) :
    (a - 1).val = a.val - 1 := by
  rw [val_sub (by rw [val_one]; refine Nat.one_le_iff_ne_zero.mpr ?_; exact (val_ne_zero a).mpr h)]
  rw [val_one]
