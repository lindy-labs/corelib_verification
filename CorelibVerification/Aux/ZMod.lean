import Aegis.Types
import Aegis.Aux.ZMod.HMul
import Mathlib.Tactic.LibrarySearch

open Sierra

instance : NeZero PRIME := ⟨by norm_num⟩

theorem ZMod.val_pos_of_ne_zero {a : ZMod n} [Fact (1 < n)] (h : a ≠ 0) : 0 < a.val := by
  apply Nat.pos_of_ne_zero
  intro h
  rw [ZMod.val_eq_zero] at h
  contradiction

theorem ZMod.val_mul_le {n : ℕ} {a b : ZMod n} : (a * b).val ≤ a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_le

theorem ZMod.val_pow {m n : ℕ} {a : ZMod n} [ilt : Fact (1 < n)] (h : a.val ^ m < n) :
    (a ^ m).val = a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    have : a.val ^ m < n := by
      by_cases ha : a = 0
      · cases ha
        by_cases hm : m = 0
        · cases hm; simp [ilt.out]
        · simp only [val_zero, ne_eq, hm, not_false_eq_true, zero_pow', Nat.zero_lt_of_lt h]
      · exact lt_of_le_of_lt
         (Nat.pow_le_pow_of_le_right (ZMod.val_pos_of_ne_zero ha) (Nat.le_succ m)) h
    rw [pow_succ, ZMod.val_mul, ih this, ← pow_succ, Nat.mod_eq_of_lt h]

theorem ZMod.val_pow_le {m n : ℕ} [Fact (1 < n)] {a : ZMod n} : (a ^ m).val ≤ a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    apply le_trans (ZMod.val_mul_le)
    apply Nat.mul_le_mul_left _ ih

instance : Fact (1 < U8_MOD) := ⟨by norm_num⟩

instance : Fact (1 < U128_MOD) := ⟨by norm_num⟩

instance : NeZero PRIME := ⟨by norm_num⟩

instance : NeZero CONTRACT_ADDRESS_MOD := ⟨by norm_num⟩

instance : Fact (CONTRACT_ADDRESS_MOD < PRIME) := ⟨by norm_num⟩

theorem ZMod.val_add_of_lt {n : ℕ} [NeZero n] {a b : ZMod n} (h : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  rw [ZMod.val_add, Nat.mod_eq_of_lt h]

theorem ZMod.val_add_of_ge {n : ℕ} [NeZero n] {a b : ZMod n} (h : a.val + b.val ≥ n) :
    (a + b).val + n = a.val + b.val := by
  rw [ZMod.val_add, Nat.add_mod_add_of_le_add_mod, Nat.mod_eq_of_lt (ZMod.val_lt _),
    Nat.mod_eq_of_lt (ZMod.val_lt _)]
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)]

theorem ZMod.val_neg {n : ℕ} [nz : NeZero n] (a : ZMod n) [na : NeZero a] :
    (- a).val = n - a.val := by
  cases n with
  | zero => cases nz; simp_all
  | succ n => 
    symm
    apply Nat.sub_eq_of_eq_add
    rw [← ZMod.val_add_of_ge, neg_add_self, ZMod.val_zero, zero_add]
    apply le_of_not_lt
    intro h
    have : 0 = val (-a) + val a := by rw[← ZMod.val_zero (n := n.succ),
      ← add_left_neg, ZMod.val_add, Nat.mod_eq_of_lt h]
    have : a.val = 0 := by linarith only [this]
    rw [ZMod.val_eq_zero] at this
    exact absurd this na.out

theorem ZMod.val_sub {n : ℕ} [NeZero n] {a b : ZMod n} (h : b.val ≤ a.val) :
    (a - b).val = a.val - b.val := by
  by_cases hb : b = 0
  · cases hb; simp
  · haveI : NeZero b := ⟨hb⟩
    rw [sub_eq_add_neg, ZMod.val_add, ZMod.val_neg, ← Nat.add_sub_assoc (le_of_lt (ZMod.val_lt _)),
      add_comm, Nat.add_sub_assoc h, Nat.add_mod_left]
    apply Nat.mod_eq_of_lt (tsub_lt_of_lt (val_lt _))

theorem ZMod.val_of_cast_of_lt {m n : ℕ} [nzm : NeZero m] [nzn : NeZero n] {a : ZMod m}
    (h : a.val < n) : (a.cast : ZMod n).val = a.val := by
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    cases n with
    | zero => cases nzn; simp_all
    | succ n => exact Fin.val_cast_of_lt h

theorem ZMod.val_ne_zero {n : ℕ}  (a : ZMod n) : a.val ≠ 0 ↔ a ≠ 0 := by
  rw [not_iff_not]
  apply ZMod.val_eq_zero

theorem ZMod.cast_rat_eq_zero_iff {m : ℕ} [NeZero m] (a : ZMod m) :
    (a : ℚ) = 0 ↔ a = 0 := by
  cases m; cases NeZero.ne 0 rfl
  rcases a with ⟨a, ha⟩
  simp only [ZMod.cast, ZMod.val, Nat.cast_eq_zero]
  constructor
  · aesop
  · intro h; injection h

theorem ZMod.cast_ZMod_eq_zero_iff_of_lt {m n : ℕ} [NeZero m] (h : m < n) (a : ZMod m) :
    (a : ZMod n) = 0 ↔ a = 0 := by
  constructor
  · intro e
    rw [ZMod.cast_eq_val, ZMod.nat_cast_zmod_eq_zero_iff_dvd] at e
    have := a.val_lt
    by_cases hz : val a = 0
    · rwa [← ZMod.val_eq_zero]
    · exfalso
      apply Nat.lt_asymm (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) e) a.val_lt) h
  · intro h; cases h; simp

theorem ZMod.cast_ZMod_ne_zero_iff_of_lt {m n : ℕ} [NeZero m] (h : m < n) (a : ZMod m) :
    (a : ZMod n) ≠ 0 ↔ a ≠ 0 := by
  rw [not_iff_not]
  apply ZMod.cast_ZMod_eq_zero_iff_of_lt h

theorem ZMod.cast_injective_of_lt {m n : ℕ} [nzm : NeZero m] (h : m < n) :
  Function.Injective (@ZMod.cast (ZMod n) _ m) := by
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    rintro ⟨x, hx⟩ ⟨y, hy⟩ f
    simp only [ZMod.cast, ZMod.val, ZMod.nat_cast_eq_nat_cast_iff',
      Nat.mod_eq_of_lt (lt_trans hx h), Nat.mod_eq_of_lt (lt_trans hy h)] at f
    apply Fin.ext
    exact f

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

theorem Nat.lt_add_left {a b c : ℕ} (h : a < c) : a < b + c := by
  rw [add_comm]
  apply Nat.lt_add_right
  assumption

theorem Nat.mul_add_div_eq_of_lt {a b c : ℕ} (h : c < b) : (b * a + c) / b = a := by
  rw [add_div (Nat.zero_lt_of_lt h)]
  simp only [mul_mod_right, zero_add, Nat.mul_div_cancel_left _ (Nat.zero_lt_of_lt h)]
  have : ¬ b ≤ c % b := by rw [not_le]; apply mod_lt _ (Nat.zero_lt_of_lt h)
  simp [Nat.div_eq_of_lt h, this]

theorem ZMod.hmul_eq_zero_iff {n : ℕ} [NeZero n] (a b : ZMod n) :
    (ZMod.hmul a b = 0) ↔ (a.val * b.val < n) := by
  cases n
  · have := NeZero.out (n := 0); simp_all only [Nat.zero_eq]
  · constructor
    · simp only [hmul]
      intro h
      injection h with h
      simp only [Nat.zero_mod, add_pos_iff, or_true, Nat.div_eq_zero_iff] at h
      exact h
    · intro h
      simp only [hmul]
      apply Fin.ext
      rw [Fin.val_zero]
      simp [Nat.div_eq_zero_iff, h]

theorem ZMod.hmul_ne_zero_iff {n : ℕ} [NeZero n] (a b : ZMod n) :
    (ZMod.hmul a b ≠ 0) ↔ (n ≤ a.val * b.val) := by
  rw [← not_lt, not_iff_not]
  apply ZMod.hmul_eq_zero_iff

theorem ZMod.val_hmul {n : ℕ} [NeZero n] (a b : ZMod n) :
    (ZMod.hmul a b).val = a.val * b.val / n := by
  cases n
  · have := NeZero.out (n := 0); simp_all only [Nat.zero_eq]
  · simp only [ZMod.hmul, ZMod.val]

theorem ZMod.val_mul_val_eq_hmul {n : ℕ} [NeZero n] (a b : ZMod n) :
    a.val * b.val = n * (hmul a b).val + (a * b).val := by
  cases n; cases NeZero.ne 0 rfl
  rw [val_mul, val_hmul]
  symm
  apply Nat.div_add_mod (a.val * b.val)

theorem ZMod.val_add_le {n : ℕ} (a b : ZMod n) : (a + b).val ≤ a.val + b.val := by
  cases n
  · simp [ZMod.val]; apply Int.natAbs_add_le
  · simp [ZMod.val_add]; apply Nat.mod_le 

theorem ZMod.val_mul_of_lt {n : ℕ} {a b : ZMod n} (h : a.val * b.val < n) :
    (a * b).val = a.val * b.val := by
  rw [ZMod.val_mul]
  apply Nat.mod_eq_of_lt h

theorem ZMod.val_nat_cast_of_lt {n a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rwa [ZMod.val_nat_cast, Nat.mod_eq_of_lt]

theorem ZMod.cast_nat_cast_of_lt {m n : ℕ} [NeZero m] (h : m < n) (a : ℕ) :
    ((a : ZMod m) : ZMod n) = a := by
  rcases m with (_|m); cases NeZero.ne 0 rfl
  haveI : NeZero n := sorry
  apply ZMod.val_injective
  simp
  sorry

#check ZMod.val_cast_of_lt

theorem Nat.eq_zero_of_mul_lt_left {a b : ℕ} (h : b * a < a) : b = 0 := by
  rw [← not_le] at h
  by_contra
  apply h
  apply Nat.le_mul_of_pos_left
  apply Nat.pos_of_ne_zero
  assumption

theorem Nat.eq_zero_of_mul_lt_right {a b : ℕ} (h : a * b < a) : b = 0 := by
  rw [mul_comm] at h; apply Nat.eq_zero_of_mul_lt_left h
