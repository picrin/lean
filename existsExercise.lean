open classical

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

lemma doubleNegate {r : Prop} : r → ¬ ¬ r := assume (Hr : r) (nHr : ¬ r), nHr Hr

lemma doubleNegateRev {r : Prop} : ¬ ¬ r → r :=
    assume (Hr : ¬ ¬ r),
        have r ∨ ¬ r, from em r,
        or.elim `r ∨ ¬r` (λ (H : r), H) (λ (H : ¬ r), false.elim (Hr H))

lemma compose {p q r : Prop} : (p → q) → (q → r) → (p → r) := sorry


lemma existsNotForall : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
    assume Hexists : (∃ x, p x),
    assume Hforall : ((∀ x, ¬ p x)),
    show false, from obtain (x : A) (P : p x ), from Hexists, Hforall x P

lemma existsFalseNotForall : (∃ x, ¬ p x) → ¬ (∀ x, p x) :=
    assume H : (∃ x, ¬ p x),
    assume H1 : (∀ x, p x),
    have H1Rewr : (∀ x, ¬ ¬ p x), from (λ (x : A), doubleNegate (H1 x)), 
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

theorem distributiveForAll : (∀ (x : A), r ∨ p x) ↔ (r ∨ ∀ (x : A), p x) :=
    iff.intro
        (λ (H : (∀ (x : A), r ∨ p x)),
        show (r ∨ ∀ (x : A), p x), from or.elim (em r)
            (λ (Pr : r), or.intro_left (∀ (y : A), p y) (Pr))
            (λ (Pnr : ¬r), or.intro_right r
                (λ (y : A), or.elim (H y)
                    (λ (Pr : r), false.elim (Pnr Pr))
                    (λ (Ppy : p y), Ppy))))
        (λ (H : (r ∨ ∀ (x : A), p x)), or.elim H
            (λ (Pr : r), ( λ (x : A), or.intro_left (p x) Pr))
            (λ (PApx : (∀ (x : A), p x)), (λ (x : A), or.intro_right (r) (PApx x))))


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

lemma existsEqNotForall : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
    iff.intro
    (assume H : (∃ x, p x),
        (λ (H1 : (∀ x, ¬ p x)),
            obtain (x : A) (Hpx : p x), from H,
            H1 x Hpx))
    (assume H : ¬ (∀ x, ¬ p x), show (∃ x, p x), from
        have S1 : (∀ x, p x ∨ ¬ p x), from (λ (x : A), em (p x)),
        have S2 : (∀ x, (∃ y, p y) ∨ ¬ p x), from (λ (x : A), or.elim (S1 x)
            (λ (Hpx : p x), or.intro_left (¬ p x) (exists.intro x Hpx))
            (λ (Hnpx : ¬ p x), or.intro_right (∃ x, p x) Hnpx)),
        have S3 : ((∃ y, p y) ∨ (∀ x, ¬ p x)),
            from (iff.elim_left (distributiveForAll A (λ (x : A), ¬ p x) (∃ y, p y))) S2,
            show (∃ y, p y), from or.elim S3 (λ (Hexists : (∃ y, p y)), Hexists) (λ (HforallNot : (∀ x, ¬ p x)), false.elim(H HforallNot)))

lemma contrapositive {p : Prop} {q : Prop} : (p → q) → (¬ q → ¬p) := 
    assume (H : (p → q)),
        assume (S1 : ¬ q),
            assume (S2 : p), S1 (H S2)

lemma iffContr {p : Prop} {q : Prop} : (p ↔ q) → (¬ p ↔ ¬ q) := 
    (λ (H : p ↔ q),
        have p → q, from iff.elim_left H,
        have q → p, from iff.elim_right H,
        iff.intro (contrapositive `q → p`) (contrapositive `p → q`))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    iff.intro
        (λ (H : ¬ ∃ x, p x), (λ (x : A),
            λ (Hpx : p x),
                H (exists.intro x Hpx)))
        (have S1 : (∃ x, p x) → ¬ (∀ x, ¬ p x), from  existsNotForall A p,
            have S2 : ¬ ¬ (∀ x, ¬ p x) → ¬ (∃ x, p x), from contrapositive S1,
            show (∀ x, ¬ p x) → ¬ (∃ x, p x), from compose
                (λ (H : (∀ x, ¬ p x)), doubleNegate H)
                (S2 : ¬ ¬ (∀ x, ¬ p x) → ¬ (∃ x, p x)))

example : (∀ x, r → p x) → (r → ∀ x, p x) := 
    (λ (H : (∀ x, r → p x)), λ (Pr : r), λ (x : A), H x Pr)

example : (r → ∀ x, p x) → (∀ x, r → p x) := 
    (λ (H : (r → ∀ x, p x)), λ (x : A), λ (Pr : r), (H Pr) x)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := iff.intro (notForallExists A p) (existsFalseNotForall A p)

example : (∀ x, p x → r) → (∃ x, p x) → r := 
    assume (H : (∀ x, p x → r)), λ (H1 : (∃ x, p x)),
        obtain (x : A) (H2 : p x), from H1, H x H2

example : ((∃ x, p x) → r) → (∀ x, p x → r) := 
    assume (H : (∃ x, p x) → r),
        λ (x : A),
            λ (Ppx : p x),
                H (exists.intro x Ppx)

example : (∃ x, p x → r) → (∀ x, p x) → r := 
    λ (H : (∃ x, p x → r)),
        λ (H1 : (∀ x, p x)),
            obtain (x : A) (Hpxr : p x → r), from H,
                Hpxr (H1 x)

example : ((∀ x, p x) → r) → (∃ x, p x → r) :=
    λ H : (∀ x, p x) → r,
        have S1 : ∀ x, (p x ∨ ¬ p x), from λ (x : A), em (p x),
        have S2 : ∀ x, (∃ x, ¬ p x) ∨ p x, from λ (x : A), or.elim (S1 x)
            (λ H : p x, or.intro_right (∃ x, ¬ p x) H)
            (λ H : ¬ p x, or.intro_left (p x) (exists.intro x H)),
        have S3 : ((∃ x, ¬ p x) ∨ ∀ x, p x),
            from (iff.elim_left (distributiveForAll A (λ x : A, p x) (∃ x, ¬ p x))) S2,
        or.elim S3
            (λ S4 : (∃ x, ¬ p x),
                obtain (x : A) (Pnx : ¬ p x), from S4,
                    exists.intro x (λ H : p x, false.elim (Pnx H)))
            (λ S5 : ∀ x, p x, exists.intro a ( λ H1 : p a, H S5))

example : (∃ x, r → p x) → (r → ∃ x, p x) :=
    λ H : (∃ x, r → p x),
        obtain (x : A) (P : r → p x), from H,
        λ (Pr : r), exists.intro x (P Pr)

example : (r → ∃ x, p x) → (∃ x, r → p x) :=
    λ H : (r → ∃ x, p x),
        have r → r → ∃ x, p x, from λ Pr : r, H,
        sorry
        --exists.intro a (λ Pr : r, obtain (x : A) (Ppx : p x), from (H Pr), Ppx)
