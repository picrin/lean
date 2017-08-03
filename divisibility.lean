def isEven (n : nat) : Prop :=
    ∃ (m : nat), 2 * m = n

lemma FourIsEven : isEven 4 :=
    exists.intro 2 (eq.refl 4)

-- (isEven 4) fourIsEven = .....

--int four = 4

--class proofsOfFour {}

--proofsOfFour myProof = ...

lemma nat.lte_zero (n : nat) : 0 ≤ n :=
    @nat.rec_on (λ k', 0 ≤ k') n (le_refl 0) (λ k (p : 0 ≤ k),
        have q : 0 ≤ 1, from nat.le_add_left 0 1,
        show (0 ≤ k + 1), from le_add_of_le_of_nonneg p q
    )

lemma lt_eq {a b c : nat} (h1 : b = c) (h2 : a < b) : (a < c) :=
    eq.subst h1 h2

lemma biggerIsBigger (a b c : nat) (h1: a < b) : (a < b + c) :=
    have H1: c + b = b + c, from nat.add_comm c b,
    lt_eq H1 (lt_add_of_nonneg_of_lt (nat.lte_zero c) h1)

lemma zero_not_succ : 0 ≠ 1 :=
    λ (m : nat.zero = (nat.succ nat.zero)),
        nat.no_confusion m

lemma same_lt {a : nat} (P : a < a) : false :=
    have H : a = a, from eq.refl a,
    ne_of_lt P H

lemma lt_neq {a b : nat} (Pab : a < b) : a ≠ b :=
    assume P : a = b,
        have P2 : b = a, from eq.symm P,
        have X : a < a, from
        calc a < b : Pab
           ... = a : P2,
        show false, from (same_lt X)


lemma cases_on_nat (rel : nat → Prop) (p0 : rel 0) (Pa : ∀ {a}, 0 < a → rel a) : (∀ n : nat, rel n) := 
    λ (n : nat),
    nat.rec_on n (p0) (
        λ (k : nat) (Pk : rel k),
            have H1 : 0 < 1 + k, from biggerIsBigger 0 1 k zero_lt_one,
            have H2 : rel (1 + k), from Pa H1,
            show rel (k + 1), from eq.subst (add_comm 1 k) H2 
    )

open classical

lemma le_add_right (a b c : nat) (h1: a < b) : (a < b + c) :=
    have H1: c + b = b + c, from nat.add_comm c b,
    lt_eq H1 (lt_add_of_nonneg_of_lt (nat.lte_zero c) h1)

lemma subst2 (a b : nat) (H : a = b) (P1 : 1 < 2 * (a + 1)) : 1 < 2 * (b + 1) := eq.subst H P1

lemma zero_le_zero (k : nat) (H : k ≤ 0) : (k = 0) := 
    have H1 : 0 ≤ k, from nat.lte_zero k,
    iff.elim_right le_antisymm_iff (and.intro H H1)

lemma one_lt_twice (m : nat) : 0 < m → 1 < 2 * m  :=
    @nat.rec_on (assume k' : nat, 0 < k' → 1 < 2 * k') m (
        assume (P : 0 < 0), (false.elim (same_lt P)))
        ( assume k : nat, assume (IH : 0 < k → 1 < 2 * k),
        show (0 < k + 1 → 1 < 2 * (k + 1)), from
        assume (P : 0 < k + 1),
            show 1 < 2 * (k + 1), from
            (or.elim (em (0 < k))
                (assume H2 : 0 < k,
                    have H4 : 1 < 2 * k, from IH H2,
                        have H8 : 1 < 2 * k + 2, from biggerIsBigger 1 (2 * k) 2 H4,
                        have H7 : 2 * k + 2 = 2 * (k + 1), by simp [mul_add],
                        show 1 < 2 * (k + 1), from eq.subst H7 H8
                    )
                (assume (H3 : 0 < k → false),
                    have H6 : k > 0 → false, from H3,
                    have H4 : k ≤ 0, from le_of_not_gt H6,
                    have H5 : k = 0, from zero_le_zero k H4,
                    have Q : (1 : nat) < 2 * (0 + 1), from of_as_true trivial,
                    show 1 < 2 * (k + 1), from (subst2 0 k (eq.symm H5)) Q
                    )
            )
        )

lemma neq.refl (m : nat) (X : 1 ≠ 2 * m) : (2 * m ≠ 1) := 
    assume H1 : 2 * m = 1,
        have H2 : 1 = 2 * m, from eq.symm H1,
            false.elim (X H2)

lemma mNotEven (m : nat) : 2 * m = 1 → false :=
    have P0 : 2 * 0 ≠ 1, from zero_not_succ,
    have P1 : ∀ m, 0 < m → 2 * m > 1, from one_lt_twice,
    have P2 : ∀ m, 0 < m → 1 ≠ 2 * m, from (λ m Pm, (lt_neq (P1 m Pm))),
    have P3 : ∀ m, 0 < m → 2 * m ≠ 1, from (λ m Pm, neq.refl m (P2 m Pm)),
    cases_on_nat (λ m, 2 * m ≠ 1) P0 P3 m


lemma OneIsNotEven : isEven 1 → false :=
    λ P1e : ∃ (m : nat), 2 * m = 1,
        exists.elim P1e (λ m : nat, λ Peven : 2 * m = 1,
            mNotEven m Peven
        )

#check @nat.rec_on

universe u



    --have cases: k < n ∨ k ≥ n, from lt_or_ge k n, or.elim cases
    --    (λ P : k < n, 
    --    )
    --    (λ P : k ≥ n, sorry)
