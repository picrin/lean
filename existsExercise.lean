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

