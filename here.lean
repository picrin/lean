variable X : Type
variable p : X -> Prop
variable r : Prop
variable a : X

open classical

theorem distributiveForAll : (∀ (x : X), r ∨ p x) → (r ∨ ∀ (x : X), p x) := 
    λ (H : (∀ (x : X), r ∨ p x)),
    show (r ∨ ∀ (x : X), p x), from or.elim (em r)
        (λ (Pr : r), or.intro_left (∀ (y : X), p y) (Pr))
        (λ (Pnr : ¬r), or.intro_right r (
            λ (y : X), or.elim (H y) 
                (λ (Pr : r), )
                (sorry)))

