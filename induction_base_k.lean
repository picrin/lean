lemma same_lt {a : nat} (P : a < a) : false :=
    have H : a = a, from eq.refl a,
    ne_of_lt P H

lemma nat.lte_zero (n : nat) : 0 ≤ n :=
    @nat.rec_on (λ k', 0 ≤ k') n (le_refl 0) (λ k (p : 0 ≤ k),
        have q : 0 ≤ 1, from nat.le_add_left 0 1,
        show (0 ≤ k + 1), from le_add_of_le_of_nonneg p q
    )

lemma lt_eq {a b c : nat} (h1 : b = c) (h2 : a < b) : (a < c) :=
    eq.subst h1 h2

lemma biggerIsBigger {a b c : nat} (h1: a < b) : (a < b + c) :=
    have H1: c + b = b + c, from nat.add_comm c b,
    lt_eq H1 (lt_add_of_nonneg_of_lt (nat.lte_zero c) h1)

def nothing_lt_zero : ∀ {k}, ¬ k < 0 := 
    assume k, nat.rec_on k
        (assume H : 0 < 0, show false, from
            have 0 = 0, from rfl, same_lt ‹0 < 0›)
        (assume k (H2 : ¬ k < 0), show k + 1 < 0 → false, from
            (assume C : k + 1 < 0,
                or.elim (lt_or_ge k 0)
                (λ H : k < 0, H2 H)
                (λ H : 0 ≤ k, or.elim (lt_or_eq_of_le H)
                    (λ H : 0 < k, have k + 1 < k, from lt_trans C H, have k + 1 < k + 1, from biggerIsBigger ‹k + 1 < k ›, same_lt ‹k + 1 < k + 1›)
                    (λ H : 0 = k, have 1 < 0, from @eq.subst _ (λ a, a + 1 < 0) _ _ (eq.symm (‹0 = k›)) C, same_lt (lt.trans ‹1 < 0› zero_lt_one)
                )
            )))

def induction_above_k
    {motive : ℕ → Prop}
    (n : ℕ) (k : ℕ)
    (base_case : motive (k + 1))
    (inductive_step : Π (a : ℕ),
        (k < a) → motive a → motive (a + 1)
    ) : k < n → motive n :=
    @nat.rec_on (assume m', k < m' → motive m') n (
        assume (P : k < 0), have H1 : false, from nothing_lt_zero P, false.elim H1
    ) (
        assume m (IH : k < m → motive m), 
            have nat_in_two : k < m ∨ k ≥ m, from (lt_or_ge k m),
            or.elim nat_in_two
            (assume H : k < m,
                have motive m, from IH H,
                show k < m + 1 → motive (m + 1), from
                    assume H1: k < m + 1,
                    show motive (m + 1), from (inductive_step m H ‹motive m›)
            )
            (assume H1 : k ≥ m,
                show k < m + 1 → motive (m + 1), from
                    assume H : k < m + 1,
                        have m < k, from sorry,
                        have m < m + 1, from nat.lt_trans ‹m < k› H,
                        have H1 : k = m, from sorry,
                        eq.subst H1 base_case
            )

            
    )

lemma one_lt_twice (m : nat) : 0 < m → 1 < 2 * m :=
    induction_above_k m 0
        (show (1 : nat) < 2 * 1, from of_as_true trivial)
        (λ k (H : 0 < k) (IH : 1 < 2 * k), show 1 < 2 * (k + 1), from
             have 1 < 2 * k + 2, from biggerIsBigger IH,
             have  2 * k + 2 = 2 * (k + 1), by simp [mul_add],
             eq.subst ‹2 * k + 2 = 2 * (k + 1)› ‹1 < 2 * k + 2›
             )