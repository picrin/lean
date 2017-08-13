inductive natural : Type
| zero : natural
| succ : natural -> natural


lemma succ_over_equality (a b : natural) (H : a = b) : (natural.succ a) = (natural.succ b) :=
    eq.rec_on H (eq.refl (natural.succ a))
    --eq.rec_on H rfl
    --eq.subst H rfl
    --eq.subst H (eq.refl (natural.succ a))
    --congr_arg (λ (n : natural), (natural.succ n)) H

variables a b : natural
variable H : (a = b)

#check (eq.rec_on H (eq.refl (natural.succ a)))


--eq H