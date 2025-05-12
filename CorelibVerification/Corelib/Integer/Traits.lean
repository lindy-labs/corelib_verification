import CorelibVerification.Corelib.Lib

aegis_spec "core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>::destruct" :=
  fun _ _ =>
  True

aegis_prove "core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>::destruct" :=
  fun _ _ => by
  intro
  exact True.intro

aegis_spec "core::traits::DestructFromDrop<core::integer::u16, core::integer::u16Drop>::destruct" :=
  fun _ _ =>
  True

aegis_prove "core::traits::DestructFromDrop<core::integer::u16, core::integer::u16Drop>::destruct" :=
  fun _ _ => by
  intro
  exact True.intro

aegis_spec "core::traits::DestructFromDrop<core::integer::u8, core::integer::u8Drop>::destruct" :=
  fun _ _ =>
  True

aegis_prove "core::traits::DestructFromDrop<core::integer::u8, core::integer::u8Drop>::destruct" :=
  fun _ _ => by
  intro
  exact True.intro

aegis_spec "core::traits::DestructFromDrop<core::integer::u64, core::integer::u64Drop>::destruct" :=
  fun _ _ =>
  True

aegis_prove "core::traits::DestructFromDrop<core::integer::u64, core::integer::u64Drop>::destruct" :=
  fun _ _ => by
  intro
  exact True.intro

aegis_spec "core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>::destruct" :=
  fun _ _ =>
  True

aegis_prove "core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>::destruct" :=
  fun _ _ => by
  intro
  exact True.intro

aegis_spec "core::traits::PanicDestructForDestruct<core::integer::u16, core::traits::DestructFromDrop<core::integer::u16, core::integer::u16Drop>>::panic_destruct" :=
  fun _ _ _ ρ =>
  ρ = ()

aegis_prove "core::traits::PanicDestructForDestruct<core::integer::u16, core::traits::DestructFromDrop<core::integer::u16, core::integer::u16Drop>>::panic_destruct" :=
  fun _ _ _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::traits::PanicDestructForDestruct<core::integer::u8, core::traits::DestructFromDrop<core::integer::u8, core::integer::u8Drop>>::panic_destruct" :=
  fun _ _ _ ρ =>
  ρ = ()

aegis_prove "core::traits::PanicDestructForDestruct<core::integer::u8, core::traits::DestructFromDrop<core::integer::u8, core::integer::u8Drop>>::panic_destruct" :=
  fun _ _ _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::traits::PanicDestructForDestruct<core::integer::u64, core::traits::DestructFromDrop<core::integer::u64, core::integer::u64Drop>>::panic_destruct" :=
  fun _ _ _ ρ =>
  ρ = ()

aegis_prove "core::traits::PanicDestructForDestruct<core::integer::u64, core::traits::DestructFromDrop<core::integer::u64, core::integer::u64Drop>>::panic_destruct" :=
  fun _ _ _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::traits::PanicDestructForDestruct<core::integer::u32, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>::panic_destruct" :=
  fun _ _ _ ρ =>
  ρ = ()

aegis_prove "core::traits::PanicDestructForDestruct<core::integer::u32, core::traits::DestructFromDrop<core::integer::u32, core::integer::u32Drop>>::panic_destruct" :=
  fun _ _ _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::traits::PanicDestructForDestruct<core::integer::u128, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>::panic_destruct" :=
  fun _ _ _ ρ =>
  ρ = ()

aegis_prove "core::traits::PanicDestructForDestruct<core::integer::u128, core::traits::DestructFromDrop<core::integer::u128, core::integer::u128Drop>>::panic_destruct" :=
  fun _ _ _ ρ => by
  rintro rfl
  rfl
