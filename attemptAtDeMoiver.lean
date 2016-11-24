
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


-- lemma deMorganHelper : ¬(p ∧ q) → ¬p :=
--   assume LHS : ¬(p ∧ q),

lemma magic (Hpq : p → q) (Hnq : ¬q) : ¬p :=
  assume Hp : p, Hnq (Hpq Hp)

check magic

lemma deMorganAnd : ¬(p ∧ q) → (¬p ∨ ¬q) :=
  assume LHS : ¬(p ∧ q),
  ((λ (Hnp : ¬p), or.intro_left (¬q) Hnp) (always (¬p)))
-- ((λ (a : Prop) (b: Prop) (Hb : a), or.intro_left b Hb) ¬p ¬q) (always ¬p)
-- (λ (Hb : a), () (always ¬p)
  

check deMorganAnd
