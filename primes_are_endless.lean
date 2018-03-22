

--def a : is_divisible 2 4 :=
--    exists.intro sorry

def magic : is_divisible 4 2 :=
    Exists.intro 2 rfl

def is_prime: nat → Prop :=
    λ p, ∀ (m : nat) (Pmdp : is_divisible p m), ((m = 1) ∨ (m = p)) ∧ (p ≠ 1)

def is_prime2: nat → Prop :=
    λ p, ∀ (k : nat) (b1 : k < p) (b2 : 1 < k), (¬ is_divisible p k)

def prime_equiv_left : ∀ (p : nat) (Pp: is_prime p), (is_prime2 p) :=
    λ (p : nat) (Pp: is_prime p),
        (λ (k : nat) (b1 : k < p) (b2 : 1 < k),
            λ (Pmdp : is_divisible p k),
                (or.elim (and.elim_left (Pp k Pmdp)) (λ P1 : k = 1, ne_of_lt b2 (eq.symm P1)) (λ P2 : k = p, ne_of_lt b1 P2)))

def func1 : nat → nat := λ (n : nat), n + 1



--def nat_in_three (k : nat) (p : nat) : k < p ∨ k = p ∨ p < k :=
--    lt_trichotomy k p

def prime_equiv_right_right : ∀ (p : nat) (Pp : is_prime2 p), ∀ (k : nat) (Pmdp : is_divisible p k), p ≠ 1 :=
    λ (p : nat) (Pp : is_prime2 p), λ (k : nat) (Pmdp : is_divisible p k), λ (Ppo : p = 1), (Pp k) sorry sorry sorry

variable q : (is_prime2 1)
variable r : nat

-- #check q 

--#check (q r : ∀ (b1 : r < 1) (b2 : 1 < r), (¬ is_divisible 1 r))

def contrapositive (p : Prop) (q : Prop) (c : Prop) : (p → q) → ¬q → ¬p :=
    λ (Ppiq : ∀ p, q), λ (Pnp : ¬q), λ Pp : p, Pnp (Ppiq Pp)

open classical


def rev_contrapositive (p : Prop) (q : Prop) (c : Prop) : (¬q → ¬p) → p → q :=
    λ (H : ¬q → ¬p), λ (P : p), have Qornq: q ∨ ¬q, from classical.em q, or.elim Qornq (λ Q : q, Q) (λ (nQ : ¬q), false.elim(H nQ P))

-- #check rev_contrapositive
-- #check piqinq

-- #check q

def ppiqpiq {p : Prop} {q : Prop} (Ppiq : p → p → q) : (p → q) := 
    λ P : p, Ppiq P P



#check (is_prime2 1)

--∀ (k : nat) (b1 : k < p) (b2 : 1 < k), (¬ is_divisible p k)



-- ∃ (x : nat) (is_prime x) ↔ ¬ ∀ (x : nat) ¬ is_prime x




def not_true_property : Prop :=
    ∀ (q : nat), q = 1

def cant_happen1 : ¬ not_true_property :=
    λ Pnot_true, 
    have a:  2 = 1, from Pnot_true 2,
    have b: 1 = 0, from congr_arg (λ (c : nat) , c - 1) a,
    show false, from nat.no_confusion (eq.symm b)


--#check nat.no_confusion (1 : nat)   0 

-- inductive some_inductive_type : 

--inductive natural : Type
--    | zero : natural
--    | succ (k : natural) : natural

def zero_ne_one_ : 0 ≠ (1 : ℕ) :=
    assume h, nat.no_confusion h

def impossible_property : Prop :=
    ∀ (Pfalse : 1 < 1), 1 = 1

def can_happen : impossible_property :=
    λ (Pfalse: 1 < 1),
        have one_ne_one : 1 ≠ 1, from (ne_of_lt Pfalse),
        have Pfalse : false, from one_ne_one (eq.refl 1),
        false.elim Pfalse

--def impossible_property : Prop :=
--    ∀ (Pfalse : false), 1 = 1

--def can_happen : impossible_property :=
--    λ (Pfalse: false),
--        false.elime Pfalse


--false.elim impossible_
 



def lt_and_gt_false (a : nat) (b : nat) (P1: a < b) (P2: b < a) : false :=
    have P3: a < a, from lt_trans P1 P2,
    (ne_of_lt P3) (eq.refl a)

def prime_equiv_right : ∀ (p : nat) (Pp : is_prime2 p), (is_prime p) := 
    sorry

-- a < b ∧ P a  

--def prime_equiv : ∀ (p : nat) (Pp: is_prime p), (is_prime2 p) :=
--    sorry

--def small_prime : is_prime 2 :=
--    sorry

--#check (a: (is_divisible 2 4))

--def is_prime: nat → Prop :=
--    λ k : nat,
--    ∀ (l : nat, ltk : l < k)

#check ((Π k : nat, k = k) : Prop)

variables v p : Prop

--constant hi : (Π (a : Prop), a)



#check ((1 = 1) : Prop)

--hi --(v ∨ p)

--#check hi (v ∨ p)

#check ((λ k: nat, eq.refl k) : (Π k : nat, k = k))

#check (1 = 1 : Prop)

#check ((Π k: Type 7, k = k) : Prop)

#check ((Π k: nat, ))

-- #check (λ k : nat, k = k) : nat -> Prop

#check (nat : Type 0)

#check (Prop : Type 0)


--#check is_prime

