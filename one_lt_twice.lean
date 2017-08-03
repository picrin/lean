-- A rigorous proof of ∀ m : nat, 0 < m → 1 < 2 * m
-- There's a class of problems I struggle to prove by induction/recursion (I'm working in CIC). The best way I can describe this class of problems is "finite cases below m, inductive case above m".

-- An "easy" example problem of this kind is ∀ m : nat, 0 < m → 1 < 2 * m
-- I can think of two approaches.

-- 1. Assume 0 < m, and recurse on m with (1 < 2 * m) as the induction motive. This works really well for the inductive case, but I struggle to prove the base case.

-- 2. Don't assume anything (except m : nat), and recurse on (0 < m → 1 < 2 * m). This works really well for the best case, but I struggle to prove the inductive case.

-- Obviously this class of problems includes much "harder" problems, such as ∀ m : nat, 4 < m → 10 < 2 * m. I suspect that such problem would require slightly more sophisticated machinery to prove succsintly, i.e. development of lists and using decidability of `10 < 2 * m` for all m ∈ [0, 4].

-- To make it clear, although I'm working in CIC, I'm not using anything too fancy/ CIC-specific, so a rigorous proof in some other foundation (say PA) could also be helpful, i.e. could help me finish the proof in CIC.

-- An attempt at the second approach is given below (I'm using the notation of "lean" proof assisstant, but I've heavily annotated my proofs to show what's going on).
/-
-- A lemma, which shows that given a natural number a, a ≮ a 
lemma same_nlt : ∀ (a : nat), ∀ (P : a < a), false :=
    -- assume a
    assume a : nat,
    -- assume a < a
    assume P : a < a,
    -- take a = a from reflexivity of equality
    have H : a = a, from eq.refl a,
    -- Using a standard library lemma a < b → a ≠ b, substitue b for a
    -- prove negation by applying a = a to a ≠ a
    ne_of_lt P H

-- The second Approach
theorem one_lt_twice2 : ∀ (m : nat), 0 < m → 1 < 2 * m  :=
    -- start with a natural number m
    assume m : nat,
    -- induction on m, with the induction motive being, for any natural k', 0 < k' → 2 * k'
    @nat.rec_on (λ k' : nat, 0 < k' → 1 < 2 * k') m (
        -- for the base case assume 0 < 0, use a lemma to derive a proof of negation, apply the principle of explosion.
        assume P : 0 < 0, false.elim (same_nlt 0 P))
        -- for the inductive case assume a proof of the motive for k, i.e. 0 < k → 1 < 2 * k
        (assume (k : nat) (InductiveHypothesis : 0 < k → 1 < 2 * k),
        -- it must be shown that 0 < k + 1 → 1 < 2 * (k + 1)
        show 0 < k + 1 → 1 < 2 * (k + 1), from
        -- assume 0 < k + 1
        assume (Q : 0 < k + 1),
            -- We have to show 2 * 1 < (k + 1).
            -- This could be easily done if we had access to a proof R of 1 < 2 * (k + 1).
            -- But in order to get Q, we have to unpack InductiveHypothesis by providing a proof of 0 < k.
            -- There's really no way to prove `0 < k` at this stage.
            -- In other words, the inductive step doesn't "know" we're above 0.
            have H1 : 0 < k, from sorry,
            -- we have to forfeit the proof attempt.
            sorry
        )
-/
open classical

lemma nat.lte_zero (n : nat) : 0 ≤ n :=
    @nat.rec_on (λ k', 0 ≤ k') n (le_refl 0) (λ k (p : 0 ≤ k),
        have q : 0 ≤ 1, from nat.le_add_left 0 1,
        show (0 ≤ k + 1), from le_add_of_le_of_nonneg p q
    )

lemma lt_eq {a b c : nat} (h1 : b = c) (h2 : a < b) : (a < c) :=
    eq.subst h1 h2

lemma le_add_right (a b c : nat) (h1: a < b) : (a < b + c) :=
    have H1: c + b = b + c, from nat.add_comm c b,
    lt_eq H1 (lt_add_of_nonneg_of_lt (nat.lte_zero c) h1)

lemma subst2 (a b : nat) (H : a = b) (P1 : 1 < 2 * (a + 1)) : 1 < 2 * (b + 1) := eq.subst H P1

lemma zero_le_zero (k : nat) (H : k ≤ 0) : (k = 0) := sorry

lemma same_lt {a : nat} (P : a < a) : false :=
    have H : a = a, from eq.refl a,
    ne_of_lt P H

lemma one_lt_twice (m : nat) : 0 < m → 1 < 2 * m  :=
    @nat.rec_on (assume k' : nat, 0 < k' → 1 < 2 * k') m (
        assume (P : 0 < 0), (false.elim (same_lt P)))
        (assume k : nat, assume (IH : 0 < k → 1 < 2 * k),
        show (0 < k + 1 → 1 < 2 * (k + 1)), from
        assume (P : 0 < k + 1),
            show 1 < 2 * (k + 1), from
            (or.elim (em (0 < k))
                (assume H2 : 0 < k,
                    have H4 : 1 < 2 * k, from IH H2,
                        have H8 : 1 < 2 * k + 2, from le_add_right 1 (2 * k) 2 H4,
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