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

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

open classical

example : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
    assume Hexists : (∃ x, p x),
    assume Hforall : ((∀ x, ¬ p x)),
    show false, from obtain (x : A) (P : p x ), from Hexists, Hforall x P
    

lemma X2 : Π (A : Type) (a : A) (p : A -> Prop), ((∀ x, p x) → false) → (p a → false)  := 
    λ (A : Type),
        λ (a : A),
            λ (p : A → Prop),
                λ (H : (∀ x, p x) → false), H 


lemma X1 : (¬ (∀ x, p x)) → (∃ x, ¬ p x) := 
    assume H : (∀ x, p x) → false,
    or.elim (em (p a))
    (assume (Hpa : p a), sorry) sorry
    --have H1 : p a → false, from λ (Hpa : (p a)), (H (λ (a : A), Hpa)), sorry

variable H : (∀ x, p x) → false


check @exists.intro

--example : (¬ (∀ x, ¬ p x)) → (∃ x, p x) :=
--    assume H_all_outer : ¬ (∀ x, ¬ p x),
--    false.elim (H_all_outer (assume (x : A), assume (Hpx : p x), exists.intro x Hpx))
    --have Hforall : (∀ x, (p x) → false), from dne Hforallnot, sorry
    --show (∃ x, p x), from (exists.intro (a : A) (false.elim (Hforall (λ (a' : A), λ (Hpx : p a'), Hpx  ))))
    --have (p a → false) → false, from Hforall a, sorry
    --show (∃ x, p x), from exists.intro



example : (∃ x, p x) → ¬ (∀ x, ¬ p x) := 
    assume Hexists : (∃ x, p x),
    assume Hforall : ((∀ x, ¬ p x)),
    show false, from obtain (x : A) (P : p x ), from Hexists, Hforall x P
    
example : ¬ (∀ x, ¬ p x) → (∃ x, p x) := 
    assume Hforall : (∀ x, (p x) → false) → false,
    show (∃ x, p x), from (exists.intro (a : A) (false.elim (Hforall (λ (a' : A), λ (Hpx : p a'), Hpx  ))))
    --have (p a → false) → false, from Hforall a, sorry
    --show (∃ x, p x), from exists.intro 

--check @exists.intro
--check exists.intro


variable x : Π (a : A), Prop

--check ((Π (a : A), Prop) : Type)

--example : (∃ x, p x) → ¬ (∀ x, ¬ p x) := 
--    assume Hexists : (∃ x, p x),
--    assume Hforall : ((∀ x, ¬ p x)),
--show false, from obtain (x : A) (P : p x ), from Hexists, Hforall x (P)


###### NOT FOR ALL ######

variables (A : Type) (p : A → Prop)

lemma right : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
    assume Hexists : (∃ x, p x),
    assume Hforall : ((∀ x, ¬ p x)),
    show false, from obtain (x : A) (P : p x ), from Hexists, Hforall x P
    
open classical
        
lemma left : ¬ (∀ x, p x) → (∃ x, ¬ p x) :=
    assume H : (∀ x, p x) → false,
    have S1 : Π y, p y ∨ ¬ p y, from take (v : A), em (p v),
    have S3 : Π y, p y ∨ (∃ x, ¬ p x), from take (y : A), or.elim (S1 y)
        (λ (Hp : p y), or.intro_left (∃ x, ¬ p x) Hp)
        (λ (Hnp : ¬ p y), or.intro_right (p y) (exists.intro y Hnp)),
    show (∃ x, ¬ p x), from by_contradiction
        (assume Hnexist : ¬ (∃ x, ¬ p x),
            have S4 : Π y, p y, from take (y : A), or.elim (S3 y)
                    (λ (Hp : p y), Hp)
                    (λ (Hexists : (∃ x, ¬ p x)), false.elim (Hnexist Hexists)),
                show false, from H S4)
