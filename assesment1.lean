-- Informally we have to show that:
-- A := ¬(p ∨ (q ∧ ¬r)) ∧ q
-- B := (¬p ∧ q) ∧ r
-- A → B ∧ B → A

-- We could do it like this:
-- A → B
-- ¬(p ∨ (q ∧ ¬r)) ∧ q →
-- (¬p ∧ ¬(q ∧ ¬r)) ∧ q →
-- ¬p ∧ (¬q ∨ r) →
-- ((¬p ∧ ¬q) ∨ (¬p ∧ r)) ∧ q →
-- ((¬p ∨ (¬p ∧ r)) ∧ (¬q ∨ (¬p ∧ r))) ∧ q →
-- (((¬p ∨ ¬p) ∧ (¬p ∨ r)) ∧ (¬q ∨ (¬p ∧ r))) ∧ q →
-- ((¬p ∨ r) ∧ (¬q ∨ ¬p) ∧ (¬q ∨ r)) ∧ q →
-- (¬p ∨ r) ∧ (¬q ∨ r) ∧ (¬q ∨ ¬p) ∧ q →
-- (¬(p ∨ q) ∨ r) ∧ ((¬q ∧ q) ∨ (¬p ∧ q)) →
-- (¬(p ∨ q) ∨ r) ∧ (¬p ∧ q) →
-- (r ∧ (¬p ∧ q)) ∨ (¬(p ∨ q) ∧ (¬p ∧ q))
-- (r ∧ (¬p ∧ q)) ∨ (¬(p ∨ q) ∧ (¬p ∧ q))
-- (r ∧ (¬p ∧ q)) ∨ (¬p ∧ ¬q ∧ ¬p ∧ q)
-- (r ∧ (¬p ∧ q)) ∨ 0

theorem equiTrans (p : Prop) (q : Prop) (r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r) :=
    assume eq1 : (p ↔ q),
        assume eq2 : (q ↔ r),
            iff.intro
                (assume Hp: p, (iff.elim_left eq2) ((iff.elim_left eq1) Hp))
                (assume Hr: r, (iff.elim_right eq1) ((iff.elim_right eq2) Hr))
