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

def gt0or0 (a : nat) : a = 0 ∨ a > 0 :=
    or.elim (em (a = 0)) (λ H : a = 0, or.intro_left (a > 0) H) (λ H : a ≠ 0, or.intro_right (a = 0) (nat.pos_of_ne_zero H))

def nat.le_add_right_of_le: ∀ (n m k : nat) (n_le_m : n <= m), n <= m + k 
    | n m 0 n_le_m := n_le_m
    | n m (k + 1) n_le_m := nat.le_succ_of_le (nat.le_add_right_of_le n m k n_le_m)

def le_succ_of_lt_right {a b : nat} : a < b → a + 1 <= b := 
    λ H : a < b,
    have S1: a + 1 < b + 1, from nat.add_lt_add_right H 1,
    show a + 1 <= b, from nat.le_of_lt_succ S1

def le_mul_right_of_pos (a b : nat) (P : b ≠ 0) : a <= a * b :=
    nat.rec_on a
        (have zero_le_zero : 0 <= 0, from le_refl 0,
        have zero_eq_b_mul_zero : 0 = b * 0, from rfl,
        have zero_comm : b * 0 = 0 * b, from mul_comm b 0,
        have zero_eq_zero_mul_b : 0 = 0 * b, from eq.trans zero_eq_b_mul_zero zero_comm,
        eq.subst zero_eq_zero_mul_b zero_le_zero)
        (λ j: nat, λ H : j <= j * b,
        have S0 : j * b = b * j, from mul_comm j b,
        have S1 : j <= b * j, from eq.subst S0 H,
        have S2 : j + 1 <= b * j + 1, from nat.add_le_add_right S1 1,
        have S8 : 0 <= b, from nat.zero_le b,
        have S9 : 1 <= b, from or.elim (iff.elim_left le_iff_lt_or_eq S8) (λ H : 0 < b, le_succ_of_lt_right H) (λ H, false.elim $ P $ eq.symm H),
        have S4 : b * (j + 1) = b * j + b, from rfl,
        have S5 : b * j + 1 <= b * j + b, from nat.add_le_add_left S9 (b * j),
        have S6 : b * j + 1 <=  b * (j + 1), from eq.subst S4 S5,
        have S7 : b * j + 1 <=  (j + 1) * b, from eq.subst (mul_comm b (j + 1)) S6,
        le_trans S2 S7)

def never_zero (a b c : nat) (H : b * a = c) (H1 : c ≠ 0): a ≠ 0 :=
    λ (Pa0 : a = 0),
    have Pbt0 : b * 0 = c, from eq.subst Pa0 H,
    have Pb0 : b * 0  = 0, from mul_zero b,
    have D1: c = 0, from eq.trans (eq.symm Pbt0) Pb0,
    show false, from H1 D1

def divisor_leq (p : nat) (m : nat) (not_zero : p ≠ 0) (divisible : is_divisible p m) : m <= p :=
    show m <= p, from (
        exists.elim divisible (λ k : nat, λ m_split : m * k = p,
        have k_not_zero: k ≠ 0, from never_zero k m p m_split not_zero,
        have m_le : m <= m * k, from (le_mul_right_of_pos m k k_not_zero), 
        eq.subst m_split m_le)
    )

def big_not_zero (a : nat) (P : 1 < a) : a ≠ 0 := 
    λ Pp : a = 0, have olt0 : 1 < 0, from eq.subst Pp P, 
        (show 1 < 0 → false, from dec_trivial) olt0

def big_greater_than_one {m : nat} (A : m ≠ 0) (B : m ≠ 1) : 1 < m :=
    have H : 0 <= m, from nat.zero_le m,
    or.elim (iff.elim_left le_iff_lt_or_eq H) (
        λ H : 0 < m, show 1 < m, from
            have H : 1 <= m, from le_succ_of_lt_right H, or.elim (iff.elim_left le_iff_lt_or_eq H) (λ H, H) (λ H, false.elim (B (eq.symm H)))
    ) (λ H, false.elim (A (eq.symm H)))

def prime_equiv_right : ∀ (p : nat) (Pp : is_prime2 p), is_prime1 p :=
    λ p : nat, λ Pp : is_prime2 p,
        and.intro (and.elim_left Pp) (
            have Ppr : ∀ (k : nat), ∀ (b1 : k < p) (b2 : 1 < k), (¬ is_divisible p k), from and.elim_right Pp,
            λ (m : nat), λ (Pmdp : is_divisible p m), or.elim(classical.em (m = 1)) (λ Pme1 : m = 1, or.intro_left (m = p) Pme1) (λ Pmep : m ≠ 1, have Pmep : m = p, from (
                have Pn0 : p ≠ 0, from big_not_zero p (and.elim_left Pp),
                have mlep : m <= p, from divisor_leq p m (Pn0) Pmdp,
                have X : m ≠ 0, from exists.elim (Pmdp) (λ (a : ℕ), λ D : m * a = p, λ H : m = 0, have A : 0 * a = p, from eq.subst H D, have I: 0 * a = 0, from zero_mul a, have R : 0 = p, from eq.subst I A, Pn0 $ eq.symm R),
                have P1lp: 1 < m, from big_greater_than_one X Pmep,
                have Pnmlp: ¬ m < p, from λ (Pmlp : m < p), Ppr m Pmlp P1lp Pmdp,
                have bleh : m < p ∨ m = p, from iff.elim_left le_iff_lt_or_eq mlep,
                or.elim bleh (λ mlp : m < p, false.elim (Pnmlp mlp)) (λ blah : m = p, blah) 
            ), show m = 1 ∨ m = p, from or.intro_right (m = 1) Pmep 
            )
        )

def prime_equiv (p : nat) : (is_prime1 p) ↔ (is_prime2 p) := 
    iff.intro (prime_equiv_left p) (prime_equiv_right p)