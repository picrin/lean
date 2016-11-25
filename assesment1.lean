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


open classical

variables p q : Prop

constant always : Π (p : Prop), p

lemma deMorganHelper : ¬(p ∧ q) → p → q → false :=
    assume (LHS : ¬(p ∧ q)) (Hp: p),
    (λ (Hq: q), LHS (and.intro Hp Hq))

lemma deMorganAndLeft : ¬(p ∧ q) → (¬p ∨ ¬q) :=
  assume LHS : ¬(p ∧ q),
  or.elim (em p)
    (λ Hp: p, or.intro_right (¬p) (deMorganHelper p q LHS Hp))
    (λ Hp: (¬p), or.intro_left (¬q) Hp)

lemma deMorganAndRight : (¬p ∨ ¬q) → ¬(p ∧ q) :=
  assume LHS : (¬p ∨ ¬q),
  always (¬(p ∧ q))

lemma deMorganAnd : ¬(p ∧ q) ↔ (¬p ∨ ¬q) := 
  iff.intro (deMorganAndLeft p q) (deMorganAndRight p q)

check deMorganAnd


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


-- this is a cheat, useful for testing. It allows us to
-- prove ANY proposition, by inhabiting that proposition's type.
constant always : Π (p : Prop), p

variables p q r : Prop

check always (p ∨ q)

-- check always (¬(p ∨ (q ∧ ¬r)) ∧ q)

lemma deMorganAnd : ¬(p ∧ q) → (¬p ∨ ¬q) :=
  assume LHS : ¬(p ∧ q),
  have leftNeg : ¬p, from always (¬p),
  have rightNeg : ¬q, from always (¬q),
or.intro_left leftNeg rightNeg
--have p from always p

check deMorganAnd

end hide

-- this is a cheat, useful for testing. It allows us to
-- prove ANY proposition, by inhabiting that proposition's type.
constant always : Π (p : Prop), p

variables p q r s : Prop

-- variable witnessNP : (¬p)

-- variable solution : (¬p ∨ ¬q)

check always (¬(p ∨ (q ∧ ¬r)) ∧ q)

-- check λ (b: Prop) (Hb : b), (λ (a : Prop) , or.intro_left b Hb) ¬p ¬q

-- check or.intro_left (¬q) witnessNP


-- check have Hnp : ¬p, from always (¬p), or.intro_left (¬q) Hnp


lemma deMorganAnd : ¬(p ∧ q) → (¬p ∨ ¬q) :=
  assume LHS : ¬(p ∧ q),
  ((λ (Hnp : ¬p), or.intro_left (¬q) Hnp) (always (¬p)))
-- ((λ (a : Prop) (b: Prop) (Hb : a), or.intro_left b Hb) ¬p ¬q) (always ¬p)
-- (λ (Hb : a), () (always ¬p)
  

check deMorganAnd







-------- ------

