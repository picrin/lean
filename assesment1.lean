-- boilerplate
import data.prod
namespace hide
open prod

-- First we need to encode logic into type theory

-- We have to allow for some statements (objects of type Prop) to become proofs (objects of type Proof).
-- "Proving a statement" will be analogous to creating an object of this type.
constant Proof: Prop → Type

-- `and` is a function, which takes 2 propositions and produces a proposition.
constant and: Prop → Prop → Prop

constant or: Prop → Prop → Prop

constant implies : Prop → Prop → Prop

-- We can create a proof of "p and q" if we have a proof of "p" and a proof of "q"
constant and_intro: Π (p q : Prop), (Proof p) -> (Proof q) -> (Proof (and p q))

-- the converse
constant and_break: Π (p q : Prop), (Proof (and p q)) -> (Proof p) × (Proof q)

-- modus ponens ((p and q) and p) -> q
constant modus_ponens: Π (p q : Prop), Proof (implies p q) -> (Proof p) -> (Proof q)

-- We can create a proof of p 

-- That's a bit ugly, becase we shouldn't need to assume that our logic *has to* have these variables.
-- I'd appreciate any feedback on how to remove this.
constants r q p : Prop

definition witness_r := Proof r

definition witness_q := Proof q

-- constant 

definition LHS : Prop := and r q

definition RHS : Prop := and q r

check (and_break r q )


-- definition Thm1  := implies LHS RHS

-- check Thm1

-- definition Thm1: Π (a b: Prop),  (Proof a)


-- check (λ x y : Prop, and x y) r q

--definition first_step := and_break a b anb

--definition second_step := and_intro b a (pr2 first_step) (pr1 first_step)

--check second_step

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


end hide
