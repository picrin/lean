open set

universe u
variable elem_type : Type u
variable a : elem_type
variable A : set elem_type
variable B : set elem_type

def notPoQ {p : Prop} {q : Prop} (H : ¬ (p ∨ q)) : (¬p ∧ ¬q) :=
    have Hnp : ¬p, from λ Hp : p, H (or.intro_left q Hp),
    have Hnq : ¬q, from λ Hq : q, H (or.intro_right p Hq),
    show ¬p ∧ ¬q, from and.intro Hnp Hnq

def prop_deMorgan {p : Prop} {q : Prop} (H : p ∧ q) : ¬ (¬p ∨ ¬q) :=
    have Pp : p, from and.elim_left H,
    have Pq : q, from and.elim_right H,
    assume (H1 : (¬p ∨ ¬q)),
        or.elim H1 (λ Hnp : ¬p, Hnp Pp) (λ Hnq: ¬q, Hnq Pq)

open classical

def dne {p : Prop} : ¬¬p → p :=
    assume H0 : ¬¬p,
    or.elim (em p)
        (assume H : p, H)
        (assume H : ¬p, false.elim (H0 H))

def set_deMorgan : a ∈ A ∩ B → a ∈ set.compl ((set.compl A) ∪ (set.compl B)) :=
    λ H : a ∈ A ∧ a ∈ B,
    show ¬ (¬ a ∈ A ∨ ¬ a ∈ B), from prop_deMorgan H

def set_deMorgan_incl : A ∩ B ⊆ set.compl ((set.compl A) ∪ (set.compl B)) :=
    have H : ∀ b : elem_type, b ∈ A ∩ B → b ∈ set.compl ((set.compl A) ∪ (set.compl B)),
        from λ (b : elem_type), @set_deMorgan elem_type b A B,
        H

def prop_deMorgan_conv {p : Prop} {q : Prop} (H : ¬ (¬p ∨ ¬q)) : p ∧ q :=
    have Pnnpnnq : ¬¬p ∧ ¬¬q, from notPoQ H,
    have Pnnp : ¬¬p, from and.elim_left Pnnpnnq,
    have Pnnq : ¬¬q, from and.elim_right Pnnpnnq,
    show p ∧ q, from and.intro (dne Pnnp) (dne Pnnq)

def set_deMorgan_conv (H : a ∈ set.compl ((set.compl A) ∪ (set.compl B))) : a ∈ A ∩ B :=
    prop_deMorgan_conv H

def set_deMorgan_incl_conv : set.compl ((set.compl A) ∪ (set.compl B)) ⊆ A ∩ B :=
    λ (b : elem_type), @set_deMorgan_conv _ b _ _

def set_deMorgan_eq : A ∩ B = set.compl ((set.compl A) ∪ (set.compl B)) :=
    sorry
