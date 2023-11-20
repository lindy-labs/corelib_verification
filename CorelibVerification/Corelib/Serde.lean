import CorelibVerification.Aux.Option
--import CorelibVerification.Aux.List
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
