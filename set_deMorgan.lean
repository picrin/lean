import data.set.basic
import topology.topological_space
open topological_space
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
    λ b, set_deMorgan_conv _ b _ _

def set_deMorgan_eq_ext : A ∩ B = set.compl ((set.compl A) ∪ (set.compl B)) :=
    subset.antisymm (set_deMorgan_incl _ _ _) (set_deMorgan_incl_conv _ _ _)

variable natSet : set nat

variable natUni : univ nat

def univSet : set nat :=
    univ

def allUniv : ∀ (n : nat), n ∈ univSet :=
    λ n,
    true.intro

def eP : 4 ∈ univSet := true.intro

def smallSet0 : set nat := {a | a = 0}

def smallSet1 : set nat := {a | a = 1}

def bigSet : set nat := {a | a = 0 ∨ a = 1}

def simpleTopo : set (set nat) := {A | A = smallSet0 ∨ A = smallSet1 ∨ A = bigSet ∨ A = univ}

def univInSimpleTopo : univ ∈ simpleTopo :=
    have H1 : @univ nat = univ, from rfl,
    have H3 : (univ = bigSet ∨ @univ nat = univ),  
        from or.intro_right (univ = bigSet) H1,
    have H4 : (univ = smallSet1 ∨ (univ = bigSet ∨ @univ nat = univ)),
        from or.intro_right (univ = smallSet1) H3,
    have H2 : (univ = smallSet0 ∨ (univ = smallSet1 ∨ (univ = bigSet ∨ @univ nat = univ))),
        from or.intro_right (univ = smallSet0) H4,
    H2

def inter_indemp : A ∩ A = A :=
    have P1 : ∀ a, a ∈ A ∩ A → a ∈ A, from λ a H,
        and.elim_left H,
    have P2 : ∀ a, a ∈ A → a ∈ A ∩ A, from λ a H,
        and.intro H H,
    set.ext (λ a, iff.intro (P1 a) (P2 a))

#check (set nat : Sort 1)

/-,-/

def open_inter (s t : set nat) : s ∈ simpleTopo → t ∈ simpleTopo → (s ∩ t) ∈ simpleTopo := 
    λ sInTopo tInTopo,
        have H1 : s = smallSet0 ∨ s = smallSet1 ∨ s = bigSet ∨ s = univ, from sInTopo,
        have H2 : t = smallSet0 ∨ t = smallSet1 ∨ t = bigSet ∨ t = univ, from tInTopo,
        show (s ∩ t = smallSet0 ∨ s ∩ t = smallSet1 ∨ s ∩ t = bigSet ∨ s ∩ t = univ), from
        or.elim H1
        (λ A1 : s = smallSet0,
            have A1Rev : smallSet0 = s, from sorry,
            or.elim H2
            (λ B1 : t = smallSet0,
                have H : smallSet0 ∩ smallSet0 = smallSet0,
                    from inter_indemp _ smallSet0,
                have H2 : s ∩ smallSet0 = smallSet0,
                    from @eq.subst _ (λ a, a ∩ smallSet0 = smallSet0) smallSet0 s A1Rev H,
                have H1 : s ∩ t = smallSet0, from @eq.subst _ (λ a, s ∩ a = smallSet0) smallSet0 t (eq.symm B1) H2,
                or.intro_left (s ∩ t = smallSet1 ∨ s ∩ t = bigSet ∨ s ∩ t = univ) H1) 
            (λ B2 : t = smallSet1 ∨ t = bigSet ∨ t = univ, sorry)
        )
        (λ A2 : s = smallSet1 ∨ s = bigSet ∨ s = univ, 
            or.elim A2
            (λ A3 : s = smallSet1, sorry)
            (λ A4 : s = bigSet ∨ s = univ,
                or.elim A4
                (λ A5 : s = bigSet, sorry)
                (λ A5 : s = univ, sorry)
            )
        )

def open_sUnion : ∀s : (set (set nat)), (∀t∈ s, t ∈ simpleTopo) → (⋃₀ s) ∈ simpleTopo :=
    sorry

def aTopology : topological_space (nat) :=
    topological_space.mk
        simpleTopo
        univInSimpleTopo
        open_inter
        open_sUnion

def setInclusion : set.subset smallSet0 bigSet :=
    λ a : nat,
        λ H : a ∈ smallSet0,
            have H1 : a = 0, from H,
            have H2 : a = 0 ∨ a = 1, from or.intro_left (a = 1) H1,
            have H3 : a ∈ bigSet, from H2,
            H3

#check λ a : set nat, sorry

--#check a : true

example : true := true.intro

--#check eP