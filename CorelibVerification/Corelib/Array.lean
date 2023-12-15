import CorelibVerification.Load

open Sierra

aegis_spec "core::array::ArrayImpl<core::felt252>::append" :=
  fun _ a b ρ _ =>
  ρ = a ++ [b]

aegis_prove "core::array::ArrayImpl<core::felt252>::append" :=
  fun _ a b ρ _ => by
  aesop

aegis_spec "core::array::SpanImpl<core::felt252>::pop_front" :=
  fun _ a ρ₁ ρ₂ =>
  (a ≠ [] ∧ ρ₁ = a.tail ∧ ρ₂ = .inl a.head!) ∨ (a = [] ∧ ρ₁ = [] ∧ ρ₂ = .inr ())

aegis_prove "core::array::SpanImpl<core::felt252>::pop_front" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_core::array::SpanImpl<core::felt252>::pop_front»
  aesop

aegis_spec "core::array::ArrayImpl<core::felt252>::span" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::array::ArrayImpl<core::felt252>::span" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::array::ArrayImpl<core::integer::u64>::span" :=
  fun _ a ρ =>
  ρ = a

aegis_prove"core::array::ArrayImpl<core::integer::u64>::span" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "core::array::ArrayImpl<core::integer::u64>::append" :=
  fun _ a b ρ _ =>
  ρ = a ++ [b]

aegis_prove "core::array::ArrayImpl<core::integer::u64>::append" :=
  fun _ a b ρ _ => by
  unfold «spec_core::array::ArrayImpl<core::integer::u64>::append»
  aesop

aegis_spec "core::array::SpanImpl<core::integer::u64>::pop_front" :=
  fun _ a ρ₁ ρ₂ =>
  (a ≠ [] ∧ ρ₁ = a.tail ∧ ρ₂ = .inl a.head!) ∨ (a = [] ∧ ρ₁ = [] ∧ ρ₂ = .inr ())

aegis_prove "core::array::SpanImpl<core::integer::u64>::pop_front" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_core::array::SpanImpl<core::integer::u64>::pop_front»
  aesop

aegis_spec "core::array::ArrayImpl<core::integer::u128>::append" :=
  fun _ a b ρ _ =>
  ρ = a ++ [b]

aegis_prove "core::array::ArrayImpl<core::integer::u128>::append" :=
  fun _ a b ρ _ => by
  unfold «spec_core::array::ArrayImpl<core::integer::u128>::append»
  aesop

aegis_spec "core::array::SpanImpl<core::integer::u128>::pop_front" :=
  fun _ a ρ₁ ρ₂ =>
  (a ≠ [] ∧ ρ₁ = a.tail ∧ ρ₂ = .inl a.head!) ∨ (a = [] ∧ ρ₁ = [] ∧ ρ₂ = .inr ())

aegis_prove "core::array::SpanImpl<core::integer::u128>::pop_front" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_core::array::SpanImpl<core::integer::u128>::pop_front»
  aesop

aegis_spec "core::array::ArrayImpl<core::integer::u128>::span" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "core::array::ArrayImpl<core::integer::u128>::span" :=
  fun _ a ρ => by
  rintro rfl
  rfl
