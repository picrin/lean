def is_divisible: nat → nat → Prop :=
    λ n m : nat, ∃ k : nat, m * k = n

def is_prime1: nat → Prop :=
    λ p, p > 1 ∧ ∀ (m : nat) (Pmdp : is_divisible p m), ((m = 1) ∨ (m = p))

def is_prime2: nat → Prop :=
    λ p, p > 1 ∧ ∀ (k : nat), (∀ (b1 : k < p) (b2 : 1 < k), (¬ is_divisible p k))

def prime_equiv_left : ∀ (p : nat) (Pp: is_prime1 p), (is_prime2 p) :=
    λ (p : nat) (Pp: is_prime1 p),
        and.intro
        (and.elim_left Pp)
        (λ (k : nat) (b1 : k < p) (b2 : 1 < k),
            λ (Pmdp : is_divisible p k),
                (or.elim (and.elim_right Pp k Pmdp)) (λ P1 : k = 1, ne_of_lt b2 (eq.symm P1)) (λ P2 : k = p, ne_of_lt b1 P2))

variable b : nat

#check eq.symm (eq.trans (mul_zero b) (eq.symm (mul_zero b)))

#check nat

variable d : nat

--#eval multiplication 0 d

def multiply_is_more (a b : nat) (b ≠ 0) : a <= a * b := sorry

def never_zero (a b c : nat) (H : b * a = c) (H1 : c ≠ 0): a ≠ 0 :=
    λ (Pa0 : a = 0),
    have Pbt0 : b * 0 = c, from eq.subst Pa0 H,
    have Pb0 : b * 0  = 0, from mul_zero b,
    have D1: c = 0, from eq.trans (eq.symm Pbt0) Pb0,
    show false, from H1 D1

def divisor_leq (p : nat) (m : nat) (not_zero : p ≠ 0) (divisible : is_divisible p m) : m <= p :=
    show m <= p, from (
        exists.elim divisible (λ k : nat, λ m_split : m * k = p,
        --have comm_m_split : k * m = p, from eq.subst m_split (@mul_comm _ _ k m),
        --have m_not_zero : m ≠ 0, from never_zero m k p comm_m_split not_zero,
        have k_not_zero: k ≠ 0, from never_zero k m p m_split not_zero,
        have m_le : m <= m * k, from (multiply_is_more m m k k_not_zero), 
        eq.subst m_split m_le)
    )

def prime_equiv_right : ∀ (p : nat) (Pp : is_prime2 p), is_prime1 p :=
    λ p : nat, λ Pp : is_prime2 p,
        and.intro (and.elim_left Pp) (
            have Ppr : ∀ (k : nat), ∀ (b1 : k < p) (b2 : 1 < k), (¬ is_divisible p k), from and.elim_right Pp,
            λ (m : nat), λ (Pmdp : is_divisible p m), or.elim(classical.em (m = 1)) (λ Pme1 : m = 1, or.intro_left (m = p) Pme1) (λ Pmep : m ≠ 1, have Pmep : m = p, from (
                have Pn0 : p ≠ 0, from sorry,
                have mlep : m <= p, from divisor_leq p m (Pn0) Pmdp,
                have P1lp: 1 < m, from sorry,
                have Pnmlp: ¬ m < p, from λ (Pmlp : m < p), Ppr m Pmlp P1lp Pmdp,
                have bleh : m < p ∨ m = p, from iff.elim_left le_iff_lt_or_eq mlep,
                or.elim bleh (λ mlp : m < p, false.elim (Pnmlp mlp)) (λ blah : m = p, blah) 
            ), show m = 1 ∨ m = p, from or.intro_right (m = 1) Pmep 
            )
        )