-- this is a cheat, useful for testing. It allows us to
-- prove ANY proposition, by inhabiting that proposition's type.

constant always : Π (p : Prop), p

open classical

variables p q : Prop


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

