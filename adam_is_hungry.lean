namespace hide

constant and : Prop → Prop → Prop
constant not : Prop → Prop
constant implies : Prop → Prop → Prop

constant Proof : Prop → Type

constant adam_is_hungry : Prop

constant proof_adam_hungry: Proof adam_is_hungry

constant adam_is_angry : Prop

constant when_adam_hungry_adam_angry : Proof (implies adam_is_hungry adam_is_angry)

constant modus_ponens : Π (p q : Type.{0}), Proof (implies p q) → (Proof p) → Proof q

check modus_ponens adam_is_hungry adam_is_angry when_adam_hungry_adam_angry proof_adam_hungry

end hide

