open classical

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

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

example : (∃ x : A, r) → r := 
    assume S1 : (∃ x : A, r),
    have S2 : (A → r → r), from (λ a : A, λ Hr : r, Hr),
    (exists.elim S1) S2
    
example : r → (∃ x : A, r) := λ (Hr : r), exists.intro a Hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := iff.intro
    (λ (HexistTogether : (∃ x, p x ∧ r)),
        obtain (x : A) (Hpxr : p x ∧ r), from HexistTogether, 
        and.intro (exists.intro x (and.elim_left Hpxr)) (and.elim_right Hpxr))
    (λ (HexistSeparately : (∃ x, p x) ∧ r),
        obtain (x : A) (Hpx : p x), from and.elim_left HexistSeparately,
        exists.intro x (and.intro Hpx (and.elim_right HexistSeparately)))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
    iff.intro
        (assume (H : (∃ x, p x ∨ q x)),
            obtain (x : A) (Por : p x ∨ q x), from H, (or.elim Por)
                (assume Hpx : p x, or.intro_left (∃ x, q x) (exists.intro x Hpx))
                (assume Hqx : q x, or.intro_right (∃ x, p x) (exists.intro x Hqx)))
        (assume (H : (∃ x, p x) ∨ (∃ x, q x)),
            or.elim H
                (assume (left : (∃ x, p x)),
                    obtain (x : A) (Hpx : p x), from left,
                        exists.intro x (or.intro_left (q x) Hpx))
                (assume (right : (∃ x, q x)),
                    obtain (x : A) (Hqx : q x), from right,
                        exists.intro x (or.intro_right (p x) Hqx)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
    iff.intro
    (assume (H : ∀ x, p x),
        (assume (H1 : (∃ x, ¬ p x)),
            obtain (x : A) (Pnx : ¬ p x), from H1,
            have p x, from H x,
            show false, from `¬ p x` `p x`))
    (assume (H: ¬ (∃ x, ¬ p x)),
        (λ (x : A), show p x, from by_contradiction
            (λ (H1 : ¬ p x), (show false, from
                have H2 : (∃ x, ¬ p x), from exists.intro x H1, H H2))))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
    iff.intro
    (assume H : (∃ x, p x),
        (λ (H1 : (∀ x, ¬ p x)),
            obtain (x : A) (Hpx : p x), from H,
            H1 x Hpx))
    (assume H : ¬ (∀ x, ¬ p x), show (∃ x, p x),
        from by_contradiction (λ (H3 : (∀ x, ¬ p x)), sorry))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := iff.intro (notForallExists A p) (existsFalseNotForall A p)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry

example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
