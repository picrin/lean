open classical

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

example : (∃ x : A, r) → r := 
    assume S1 : (∃ x : A, r),
    have S2 : (A → r → r), from (λ a : A, λ Hr : r, Hr),
    (exists.elim S1) S2

theorem t1 : r → (Exists (λ x : A, r)) := assume Hr : r, exists.intro a Hr

example : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r := assume H : (Exists (λ x : A, p x ∧ r)),
    have S1 : (Π (x : A), p x ∧ r → ((∃ x, p x) ∧ r)) → (∃ x, p x) ∧ r, from exists.elim H,
    have S2 : Π (x : A), p x ∧ r → ((∃ x, p x) ∧ r), from
        assume x : A,
            take S3 : p x ∧ r, and.intro (exists.intro x (and.elim_left S3)) (and.elim_right S3),
    S1 S2

example : (∃ x, p x) ∧ r → (∃ x, p x ∧ r) :=
    assume H : (∃ x, p x) ∧ r,
    have S1 : (∃ x, p x), from and.elim_left H,
    have S2 : r, from and.elim_right H,
    obtain (x : A) (K : p x), from S1, exists.intro x (and.intro K S2)

example : (∃ x, p x) ∧ r → (∃ x, p x ∧ r) :=
    assume H : (∃ x, p x) ∧ r,
    have S1 : (∃ x, p x), from and.elim_left H,
    have S2 : r, from and.elim_right H,
    have S3 : (Π (x : A), p x → (∃ x, p x ∧ r)) → (∃ x, p x ∧ r), from exists.elim S1,
    have S4 : (Π (x : A), p x → (∃ x, p x ∧ r)), from
        (assume x : A, take K : p x, exists.intro x (and.intro K S2)),
    S3 S4

--open classical

--example : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

example : (∃ x, p x) → ¬ (∀ x, ¬ p x) := 
    assume Hexists : (∃ x, p x),
    assume Hforall : ((∀ x, ¬ p x)),
    show false, from obtain (x : A) (P : p x ), from Hexists, Hforall x P
    


------ NOT FOR ALL ------

lemma doubleNegate : r → ¬ ¬ r := assume (Hr : r) (nHr : ¬ r), nHr Hr

lemma existsNotForall : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
    assume Hexists : (∃ x, p x),
    assume Hforall : ((∀ x, ¬ p x)),
    show false, from obtain (x : A) (P : p x ), from Hexists, Hforall x P

lemma existsFalseNotForall : (∃ x, ¬ p x) → ¬ (∀ x, p x) :=
    assume H : (∃ x, ¬ p x),
    assume H1 : (∀ x, p x),
    have H1Rewr : (∀ x, ¬ ¬ p x), from (λ (x : A), doubleNegate (p x) (H1 x)), 
    have flema : (∃ x, ¬ p x) → ¬ (∀ x, ¬ ¬ p x), from (existsNotForall A (λ (a : A), ¬ p a)),
    have notForall : ¬ (∀ x, ¬ ¬ p x), from flema H,
    show false, from notForall H1Rewr

open classical

lemma notForallExists : ¬ (∀ x, p x) → (∃ x, ¬ p x) :=
    assume H : (∀ x, p x) → false,
    have S1 : Π y, p y ∨ ¬ p y, from take (y : A), em (p y),
    have S3 : Π y, p y ∨ (∃ x, ¬ p x), from take (y : A), or.elim (S1 y)
        (λ (Hp : p y), or.intro_left (∃ x, ¬ p x) Hp)
        (λ (Hnp : ¬ p y), or.intro_right (p y) (exists.intro y Hnp)),
    show (∃ x, ¬ p x), from by_contradiction
        (assume Hnexist : ¬ (∃ x, ¬ p x),
            have S4 : Π y, p y, from take (y : A), or.elim (S3 y)
                (λ (Hp : p y), Hp)
                (λ (Hexists : (∃ x, ¬ p x)), false.elim (Hnexist Hexists)),
            show false, from H S4)

theorem notForall : ¬ (∀ x, p x) ↔ (∃ x, ¬ p x) := iff.intro (notForallExists A p) (existsFalseNotForall A p)
