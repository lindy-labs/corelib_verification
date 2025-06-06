import Aegis.Tactic
import CorelibVerification.Corelib.Array

open Sierra

aegis_spec "core::panic_with_felt252" :=
  fun _ a ρ =>
  ρ = ((), [a])

aegis_prove "core::panic_with_felt252" :=
  fun _ a ρ => by
  unfold «spec_core::panic_with_felt252»
  aesop

aegis_spec "core::Felt252Sub::sub" :=
  fun _ a b ρ =>
  ρ = a - b

aegis_prove "core::Felt252Sub::sub" :=
  fun _ a b ρ => by
  rintro rfl
  rfl

aegis_spec "core::Felt252PartialEq::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "core::Felt252PartialEq::eq" :=
  fun _ a b ρ => by
  unfold «spec_core::Felt252PartialEq::eq»
  rintro (⟨h,rfl⟩|h)
  · aesop (add forward safe eq_of_sub_eq_zero)
  · aesop

aegis_spec "core::BoolNot::not" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool (¬ a)

aegis_prove "core::BoolNot::not" :=
  fun _ a ρ => by
  rintro rfl
  unfold «spec_core::BoolNot::not»
  simp

aegis_spec "core::Felt252PartialEq::ne" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a ≠ b)

aegis_prove "core::Felt252PartialEq::ne" :=
  fun _ a b ρ => by
  unfold «spec_core::Felt252PartialEq::ne»
  aesop

aegis_spec "core::panic_with_const_felt252<608642107937639184217240406363762551>" :=
  fun _ ρ =>
  ρ = ⟨(), [608642107937639184217240406363762551]⟩

aegis_prove "core::panic_with_const_felt252<608642107937639184217240406363762551>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<155775200863573220731881744814274539383>" :=
  fun _ ρ =>
  ρ = ⟨(), [155775200863573220731881744814274539383]⟩

aegis_prove "core::panic_with_const_felt252<155775200863573220731881744814274539383>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<155785504327651875780457110017927835511>" :=
  fun _ ρ =>
  ρ = ⟨(), [155785504327651875780457110017927835511]⟩

aegis_prove "core::panic_with_const_felt252<155785504327651875780457110017927835511>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<155801121783046687566683549401418067831>" :=
  fun _ ρ =>
  ρ = ⟨(), [155801121783046687566683549401418067831]⟩

aegis_prove "core::panic_with_const_felt252<155801121783046687566683549401418067831>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<39878429859761676908720221312622923640695>" :=
  fun _ ρ =>
  ρ = ⟨(), [39878429859761676908720221312622923640695]⟩

aegis_prove "core::panic_with_const_felt252<39878429859761676908720221312622923640695>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<8445995464992694320>" :=
  fun _ ρ =>
  ρ = ⟨(), [8445995464992694320]⟩

aegis_prove "core::panic_with_const_felt252<8445995464992694320>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<2161814014192570802224>" :=
  fun _ ρ =>
  ρ = ⟨(), [2161814014192570802224]⟩

aegis_prove "core::panic_with_const_felt252<2161814014192570802224>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<2161886914012515606576>" :=
  fun _ ρ =>
  ρ = ⟨(), [2161886914012515606576]⟩

aegis_prove "core::panic_with_const_felt252<2161886914012515606576>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<32994284134408240>" :=
  fun _ ρ =>
  ρ = ⟨(), [32994284134408240]⟩

aegis_prove "core::panic_with_const_felt252<32994284134408240>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<8444590289132396592>" :=
  fun _ ρ =>
  ρ = ⟨(), [8444590289132396592]⟩

aegis_prove "core::panic_with_const_felt252<8444590289132396592>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<8445148841039306800>" :=
  fun _ ρ =>
  ρ = ⟨(), [8445148841039306800]⟩

aegis_prove "core::panic_with_const_felt252<8445148841039306800>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<5420154128225384396790819266608>" :=
  fun _ ρ =>
  ρ = ⟨(), [5420154128225384396790819266608]⟩

aegis_prove "core::panic_with_const_felt252<5420154128225384396790819266608>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<39879774624085075084607933104993585622903>" :=
  fun _ ρ =>
  ρ = ⟨(), [39879774624085075084607933104993585622903]⟩

aegis_prove "core::panic_with_const_felt252<39879774624085075084607933104993585622903>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<39879774624079483812136948410799859986295>" :=
  fun _ ρ =>
  ρ = ⟨(), [39879774624079483812136948410799859986295]⟩

aegis_prove "core::panic_with_const_felt252<39879774624079483812136948410799859986295>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<39879774624083218221772669863277689073527>" :=
  fun _ ρ =>
  ρ = ⟨(), [39879774624083218221772669863277689073527]⟩

aegis_prove "core::panic_with_const_felt252<39879774624083218221772669863277689073527>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<375233589013918064796019>" :=
  fun _ ρ =>
  ρ = ⟨(), [375233589013918064796019]⟩

aegis_prove "core::panic_with_const_felt252<375233589013918064796019>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<1749165063169615148890104124711417950509560691>" :=
  fun _ ρ =>
  ρ = ⟨(), [1749165063169615148890104124711417950509560691]⟩

aegis_prove "core::panic_with_const_felt252<1749165063169615148890104124711417950509560691>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<476442828812030857794232422692155113556837216824>" :=
  fun _ ρ =>
  ρ = ⟨(), [476442828812030857794232422692155113556837216824]⟩

aegis_prove "core::panic_with_const_felt252<476442828812030857794232422692155113556837216824>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<7269940625183577871052929410204041567614516>" :=
  fun _ ρ =>
  ρ = ⟨(), [7269940625183577871052929410204041567614516]⟩

aegis_prove "core::panic_with_const_felt252<7269940625183577871052929410204041567614516>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<7269940625183576940180048306939577043858226>" :=
  fun _ ρ =>
  ρ = ⟨(), [7269940625183576940180048306939577043858226]⟩

aegis_prove "core::panic_with_const_felt252<7269940625183576940180048306939577043858226>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<7269940625183576326045731942707956293120310>" :=
  fun _ ρ =>
  ρ = ⟨(), [7269940625183576326045731942707956293120310]⟩

aegis_prove "core::panic_with_const_felt252<7269940625183576326045731942707956293120310>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<110930490496575599150170734222081291576>" :=
  fun _ ρ =>
  ρ = ⟨(), [110930490496575599150170734222081291576]⟩

aegis_prove "core::panic_with_const_felt252<110930490496575599150170734222081291576>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<9163530612918341685758827355588318787825527>" :=
  fun _ ρ =>
  ρ = ⟨(), [9163530612918341685758827355588318787825527]⟩

aegis_prove "core::panic_with_const_felt252<9163530612918341685758827355588318787825527>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<35795041456712272209994989265157601652599>" :=
  fun _ ρ =>
  ρ = ⟨(), [35795041456712272209994989265157601652599]⟩

aegis_prove "core::panic_with_const_felt252<35795041456712272209994989265157601652599>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<29721761890975875353235833581453094220424382983267374>" :=
  fun _ ρ =>
  ρ = ⟨(), [29721761890975875353235833581453094220424382983267374]⟩

aegis_prove "core::panic_with_const_felt252<29721761890975875353235833581453094220424382983267374>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<573087285299505011920718992710461799>" :=
  fun _ ρ =>
  ρ = ⟨(), [573087285299505011920718992710461799]⟩

aegis_prove "core::panic_with_const_felt252<573087285299505011920718992710461799>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<6713199>" :=
  fun _ ρ =>
  ρ = ⟨(), [6713199]⟩

aegis_prove "core::panic_with_const_felt252<6713199>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::assert" :=
  fun _ a err ρ =>
  a = Bool.toSierraBool .true ∧ ρ = .inl () ∨
    a = Bool.toSierraBool .false ∧ ρ = .inr ((), [err])

aegis_prove "core::assert" :=
  fun _ a err ρ => by
  unfold_spec "core::assert"
  aesop

aegis_spec "core::Felt252Default::default" :=
  fun _ ρ =>
  ρ = 0

aegis_prove "core::Felt252Default::default" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::Felt252Mul::mul" :=
  fun _ a b ρ =>
  ρ = a * b

aegis_prove "core::Felt252Mul::mul" :=
  fun _ a b ρ => by
  rintro rfl
  rfl

aegis_spec "core::Felt252Add::add" :=
  fun _ a b ρ =>
  ρ = a + b

aegis_prove "core::Felt252Add::add" :=
  fun _ a b ρ => by
  rintro rfl
  rfl
