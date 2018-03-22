def is_divisible: nat → nat → Prop :=
    λ n m : nat, ∃ k : nat, m * k = n

def is_prime1: nat → Prop :=
    λ p, p > 1 → ∀ (m : nat) (Pmdp : is_divisible p m), ((m = 1) ∨ (m = p))

def is_prime2: nat → Prop :=
    λ p, p > 1 → ∀ (k : nat), (∀ (b1 : k < p) (b2 : 1 < k), (¬ is_divisible p k))

def prime_equiv_left : ∀ (p : nat) (Pp: is_prime1 p), (is_prime2 p) :=
    λ (p : nat) (Pp: is_prime1 p),
        λ Ppgto : p > 1,
        (λ (k : nat) (b1 : k < p) (b2 : 1 < k),
            λ (Pmdp : is_divisible p k),
                (or.elim ((Pp Ppgto k Pmdp) )) (λ P1 : k = 1, ne_of_lt b2 (eq.symm P1)) (λ P2 : k = p, ne_of_lt b1 P2))

--#check is_prime1 1

def a : 1 > 1 := sorry

variable b : is_prime1 1 

#check b a