-- `variable` is an unfortunate name, conflicting
-- with usual meaning of the word.
-- `p` and `q` are *implicit parameters*
-- passed to our functions. (All lemmas and theorems
-- will be functions)
variables p q : Prop


-- These introduction and elimination rules
-- are analogous to and.intro and and.elim,
-- but they work with falsehoods as opposed to truths.

-- `lemma` is syntactic sugar for `definition`, 
lemma andFalseElimRight : ¬(p ∧ q) → (p → ¬q) :=
    -- `assume` is syntactic sugar for `λ`
    assume (LHS : ¬(p ∧ q)) (Hp: p),
    (λ (Hq: q), LHS (and.intro Hp Hq))


lemma andFalseElimLeft : ¬(p ∧ q) → (q → ¬p) :=
    assume (LHS : ¬(p ∧ q)) (Hq: q),
    (λ (Hp: p), LHS (and.intro Hp Hq))


lemma andFalseIntroLeft : ¬p → ¬(p ∧ q) :=
    assume (LHS : ¬p),
    (λ Hnpq: (p ∧ q), LHS (and.elim_left Hnpq))


lemma andFalseIntroRight : ¬p → ¬(q ∧ p) :=
    assume (LHS : ¬p),
    (λ Hnpq: (q ∧ p), LHS (and.elim_right Hnpq))


-- We need classical logic for excluded middle to prove de Morgan's.
open classical


-- Prove de Morgan's.
lemma deMorganAndLeft : ¬(p ∧ q) → (¬p ∨ ¬q) :=
  assume LHS : ¬(p ∧ q),
  -- The claim easily follows from excluded middle on p 
  or.elim (em p) -- (p ∨ ¬p)
    -- if p, we have to first show that ¬q, and then introduce desired disjunction (¬p ∨ ¬q)
    (λ Hp: p, or.intro_right (¬p) (andFalseElimRight p q LHS Hp))
    -- if ¬p, we can simply introduce desired disjunction (¬p ∨ ¬q)
    (λ Hp: (¬p), or.intro_left (¬q) Hp)


lemma deMorganAndRight : (¬p ∨ ¬q) → ¬(p ∧ q) :=
  assume LHS : (¬p ∨ ¬q),
  or.elim LHS (andFalseIntroLeft p q) (andFalseIntroRight q p)


-- If this line type-checks correctly, then the theorem is proven.
-- In order to be completely certain about the proof,
-- one has to additionally check that:
-- 1. No additional `axioms` have been defined.
--    Some axioms can lead to inconsistent foundations.
-- 2. The statement of the theorem is correct, i.e.
--    in our case deMorganAnd really *does* correspond
--    to one of the theorems commonly referred to as de Morgan's laws.
theorem deMorganAnd (p : Prop) (q: Prop) : ¬(p ∧ q) ↔ (¬p ∨ ¬q) :=
  iff.intro (deMorganAndLeft p q) (deMorganAndRight p q)


-- prints the type of deMorganAnd.
check deMorganAnd

