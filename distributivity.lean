variables p q r : Prop

theorem distributivity : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    assume LHS : p ∧ (q ∨ r),
    have Pp : p, from and.elim_left(LHS),
    have Pqor : (q ∨ r), from and.elim_right(LHS),
    have Poe : (q → (p ∧ q) ∨ (p ∧ r)) → (r → (p ∧ q) ∨ (p ∧ r)) → (p ∧ q) ∨ (p ∧ r), from or.elim Pqor,
    have qi : q → (p ∧ q) ∨ (p ∧ r), from
        (assume Pq : q,
        have poq : p ∧ q, from and.intro Pp Pq,
        show (p ∧ q) ∨ (p ∧ r), from or.intro_left (p ∧ r) poq
        ),
    have ri : (r → (p ∧ q) ∨ (p ∧ r)), from
        (assume Pr : r,
        have por : p ∧ r, from and.intro Pp Pr,
        show (p ∧ q) ∨ (p ∧ r), from or.intro_right (p ∧ q) por
        ),
    show (p ∧ q) ∨ (p ∧ r), from Poe qi ri

