open classical

variables p q r : Prop

lemma andFalseElimRight : ¬(p ∧ q) → p → ¬q :=
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

theorem deMorganAnd : ¬(p ∧ q) ↔ (¬p ∨ ¬q) :=
    iff.intro (deMorganAndLeft p q) (deMorganAndRight p q)

theorem deMorganOrRight : (¬p ∧ ¬q) → ¬(p ∨ q) :=
    λ (LHS : (¬p) ∧ (¬q)),
        λ (Hporq : p ∨ q),
            or.elim Hporq
            (λ (Hp : p), (and.elim_left LHS) Hp)
            (λ (Hq : q), (and.elim_right LHS) Hq)


theorem doubleNeg : ¬¬p → p :=
    λ (H : ¬¬p),
        or.elim (em p)
            (assume Hp : p, Hp)
            (assume Hnp : ¬p, absurd Hnp H)

theorem contraposition (Hpq : p → q) (Hnq : ¬q) : ¬p :=
    not.intro
        (assume Hp : p,
        show false, from not.elim Hnq (Hpq Hp))

theorem contrapositionRev : (¬q → ¬p) → (p → q) :=
    λ (LHS : (¬q → ¬p)),
        λ (Hp : p), 
            (doubleNeg q (λ (Hq : ¬q), LHS Hq Hp))


theorem doubleNegRev : p → ¬¬p :=
    λ (Hp : p), or.elim (em ¬p)
            (assume Hnp : ¬p, absurd Hp Hnp)
            (assume Hnnp : ¬¬p, Hnnp)

theorem deMorganContra : ¬(¬p ∧ ¬q) → ¬¬(p ∨ q) :=
    λ (LHS: ¬(¬p ∧ ¬q)), doubleNegRev (p ∨ q) (or.elim ((deMorganAndLeft ¬p ¬q) LHS)
        (λ (H1: ¬¬p), or.intro_left q (doubleNeg p H1))
        (λ (H2: ¬¬q), or.intro_right p (doubleNeg q H2)))

theorem deMorganOrLeft : ¬(p ∨ q) → (¬p ∧ ¬q) := 
    contrapositionRev (¬(p ∨ q)) (¬p ∧ ¬q) (deMorganContra p q)


theorem equiTrans : (p ↔ q) → (q ↔ r) → (p ↔ r) :=
    assume eq1 : (p ↔ q),
        assume eq2 : (q ↔ r),
            iff.intro
                (assume Hp: p, (iff.elim_left eq2) ((iff.elim_left eq1) Hp))
                (assume Hr: r, (iff.elim_right eq1) ((iff.elim_right eq2) Hr))

theorem distributivity : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    λ (LHS : p ∧ (q ∨ r)),
    or.elim (and.elim_right LHS)
        (λ (Hq : q),
            or.intro_left
            (p ∧ r)
            (and.intro (and.elim_left LHS) Hq))
        (λ (Hr : r),
            or.intro_right
            (p ∧ q)
            (and.intro (and.elim_left LHS) Hr))

lemma s1 : ¬(p ∨ (q ∧ ¬r)) ∧ q ↔ (¬p ∧ ¬(q ∧ ¬r)) ∧ q :=
    iff.intro
        (assume (LHS : ¬(p ∨ (q ∧ ¬r)) ∧ q),
            and.intro
                (deMorganOrLeft p (q ∧ ¬r)
                    (and.elim_left LHS))
                (and.elim_right LHS))
        (assume (LHS : (¬p ∧ ¬(q ∧ ¬r)) ∧ q),
            and.intro
                (deMorganOrRight p (q ∧ ¬r)
                    (and.elim_left LHS))
                (and.elim_right LHS))

lemma doubleNegOr : (q ∨ r) → (q ∨ ¬¬r) :=
    assume (LHS : (q ∨ r)), or.elim LHS
        (λ (Hq : q), or.intro_left (¬¬r) Hq)
        (λ (Hr : r), or.intro_right q (doubleNegRev r Hr))

lemma doubleNegOrRev : (q ∨ ¬¬r) → (q ∨ r) :=
    assume (LHS : (q ∨ ¬¬r)), or.elim LHS
        (λ (Hq : q), or.intro_left (r) Hq)
        (λ (Hr : ¬¬r), or.intro_right q (doubleNeg r Hr))


lemma s2 : (¬p ∧ ¬(q ∧ ¬r)) ∧ q → (¬p ∧ (¬q ∨ r)) ∧ q :=
    assume (LHS : (¬p ∧ ¬(q ∧ ¬r)) ∧ q),
        and.intro
        (and.intro (and.elim_left (and.elim_left LHS))
        (doubleNegOrRev (¬q) r (deMorganAndLeft q (¬r) (and.elim_right (and.elim_left LHS)))))
        (and.elim_right LHS)

            
-- Informally we have to show that:
-- ¬(p ∨ (q ∧ ¬r)) ∧ q ↔
-- (¬p ∧ q) ∧ r

-- We could do it like this:
-- ¬(p ∨ (q ∧ ¬r)) ∧ q ↔ (s1)
-- (¬p ∧ ¬(q ∧ ¬r)) ∧ q ↔ (s2)
-- ¬p ∧ (¬q ∨ r) ∧ q ↔ (s3)
-- ((¬p ∧ ¬q) ∨ (¬p ∧ r)) ∧ q ↔
-- ((¬p ∨ (¬p ∧ r)) ∧ (¬q ∨ (¬p ∧ r))) ∧ q ↔
-- (((¬p ∨ ¬p) ∧ (¬p ∨ r)) ∧ (¬q ∨ (¬p ∧ r))) ∧ q ↔
-- ((¬p ∨ r) ∧ (¬q ∨ ¬p) ∧ (¬q ∨ r)) ∧ q ↔
-- (¬p ∨ r) ∧ (¬q ∨ r) ∧ (¬q ∨ ¬p) ∧ q ↔
-- (¬(p ∨ q) ∨ r) ∧ ((¬q ∧ q) ∨ (¬p ∧ q)) ↔
-- (¬(p ∨ q) ∨ r) ∧ (¬p ∧ q) ↔
-- (r ∧ (¬p ∧ q)) ∨ (¬(p ∨ q) ∧ (¬p ∧ q)) ↔
-- (r ∧ (¬p ∧ q)) ∨ (¬(p ∨ q) ∧ (¬p ∧ q)) ↔
-- (r ∧ (¬p ∧ q)) ∨ (¬p ∧ ¬q ∧ ¬p ∧ q) ↔
-- (r ∧ (¬p ∧ q)) ∨ 0
