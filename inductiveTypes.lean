import init.data 

namespace hide
definition add (n m : nat) : nat :=
    nat.rec_on m n (
        assume (k : nat),
            assume (IH : nat),
                nat.succ IH)

lemma ladd (n m : nat) : nat :=
    nat.rec_on n m (
        assume (k : nat),
            assume (IH : nat),
                nat.succ IH)

lemma fold_add_right (n : nat) : (n = add nat.zero n) :=
    nat.rec_on n (eq.refl nat.zero) (
        assume y : nat,
            assume H : y = add nat.zero y,
                have H2 : nat.succ y = nat.succ (add nat.zero y), from eq.subst H rfl,
                have H1 : nat.succ (add nat.zero y) = add nat.zero (nat.succ y), from rfl,
                show nat.succ y = add nat.zero (nat.succ y), from
                    eq.trans H2 H1)

theorem add_rintro_succ (n m : nat):
    (nat.succ (add n m) = (add n (nat.succ m))) :=
        rfl

theorem add_lintro_succ (n m : nat):
    (nat.succ (add n m) = (add (nat.succ n) m)) :=
        nat.rec_on m (rfl) (
        assume k : nat,
            assume IH : (nat.succ (add n k) = (add (nat.succ n) k)),
                have H1 : nat.succ (nat.succ (add n k)) = nat.succ (add n (nat.succ k)), from eq.subst (add_rintro_succ n k) rfl,
                have H2 : (nat.succ (add (nat.succ n) k)) = (add (nat.succ n) (nat.succ k)), from (add_rintro_succ (nat.succ n) k),
                have H3 : (nat.succ (nat.succ (add n k)) = nat.succ (add (nat.succ n) k)), from eq.subst IH rfl,
                show nat.succ (add n (nat.succ k)) = (add (nat.succ n) (nat.succ k)),
                from eq.symm (eq.trans (eq.trans H2 (eq.symm H3)) H1))

theorem add_swap_ladd (n m : nat) : ladd n m = add m n :=
    nat.rec_on n (rfl) (
        assume (k : nat),
            assume (IH : ladd k m = add m k),
                eq.subst IH (rfl))

theorem add_comm (n m : nat) : add n m = add m n :=
    @nat.rec_on (λ k : nat, add n k = add k n) m (fold_add_right n) (
        assume (y : nat),
            assume (IH : add n y = add y n),
                have H1 : nat.succ (add n y) = nat.succ (add y n), from eq.subst IH rfl,
                have H2 : nat.succ (add n y) = (add n (nat.succ y)), from add_rintro_succ n y,
                have H3 : nat.succ (add y n) = (add (nat.succ y) n), from add_lintro_succ y n,
                eq.trans (eq.trans (eq.symm H2) H1) H3)

#check @nat.rec_on

theorem add_is_equal (n m : nat) : (add n m) = (ladd n m) :=
    have H1 : (add n m) = (add n m), from rfl,
    have H2 : (add n m) = (add m n), from add_comm n m,
    have H3 : ladd n m = add m n, from add_swap_ladd n m,
    eq.trans (eq.trans H1 H2) (eq.symm H3)

definition mul (n m : nat) : (nat) :=
    nat.rec_on m (nat.zero) (
        assume (m' : nat),
            assume (IH : nat),
                add n IH
    )

definition mul_diff (n m : nat) : (nat) :=
    nat.rec_on m (nat.zero) (
        assume (m' : nat),
            assume (IH : nat),
                add IH n
    )

theorem mul_is_equal (n m : nat) : mul n m = mul_diff n m :=
    nat.rec_on m (rfl) (
        assume (m' : nat),
            assume (IH : mul n m' = mul_diff n m'),
                show mul n (nat.succ m') = mul_diff n (nat.succ m'), from
                have H1 : mul n (nat.succ m') = add n (mul n m'), from rfl,
                have H2 : add (mul_diff n m') n = mul_diff n (nat.succ m'), from rfl,
                have H3 : add (mul n m') n = add (mul_diff n m') n, from eq.subst IH rfl,
                have H4 : add n (mul n m') = add (mul n m') n, from add_comm n (mul n m'),
                have H5 : add n (mul n m') = add (mul_diff n m') n, from eq.trans H4 H3,
                eq.trans (eq.trans H1 H5) H2
   )

universes u v

inductive natural : Type
| zero : natural
| succ : natural → natural

-- How to write a definition of the dependent product using Pi types?

-- I'm working through [chapter 7 -- inductive types](https://leanprover.github.io/theorem_proving_in_lean/#07_Inductive_Types.html) of "Theorem Proving in Lean".

-- I'd like to know how to write the definition of dependent product in a more expanded or "primitive" form.

-- It looks like the definition given in the tutorial automatically infers some detail:
inductive prod1 (α : Type u) (β : Type v)
| mk : α → β → prod1

-- Some experimentation allows to fill in the detail:
inductive prod2 (α : Type u) (β : Type v) : Type (max u v)
| mk : α → β → prod2

-- What is the correct way to write prod3?

-- Finally, is the following definition equivalent to `prod1` and `prod2`, i.e. can the type checker always infer the correct type universe for α and β?
inductive prod4 (α : Type*) (β : Type*)
| mk : α → β → prod4

inductive sum (a : Type u) (b : Type v)
| inl {} : a → sum
| inr {} : b → sum

def pr1 (a : Type) (b : Type) (p : prod a b) : a :=
prod.rec_on p (λ a' : a, λ b' : b, a')

def pr2 (a : Type) (b : Type) (p : prod a b) : b :=
prod.rec_on p (λ a' : a, λ b' : b, b')

inductive list (A : Type) : Type

def cons : Π (A : Type), A → list A → list A :=
    sorry


#check prod

--#check sum.inl 1 (λ a : sorry, sorry)
universe x

inductive Exists {α : Sort u} (rel : α → Prop) : Prop
| intro : Π (a : α), rel a → Exists

lemma SixIsEven : (Exists (λ (n : nat), 2 * n = 6)) :=
    Exists.intro 3 (eq.refl 6)

def isEven (n : nat) : Prop :=
    ∃ (m : nat), 2 * m = n

lemma EightIsEven : isEven 8 := 
    exists.intro 4 (eq.refl 8)


        
#check @nat.rec_on

--#check Exists.intro 4 (eq.refl 8)

--#check aIsEven 2 

#reduce (λ n : nat, (eq.refl (2 * n))) 3

lemma exists.elim {α : Sort u} {rel : α → Prop} {p : Prop}
  (h1 : Exists rel) (h2 : ∀ (a : α), rel a → p) : p :=
Exists.rec h2 h1


variables p q r : Prop
variable Pp : p
variable paq : p ∨ q
variable rel : nat → Prop
variable pExists : @Exists nat rel

#check @Exists.intro nat rel

end hide

variables n m : nat

theorem works (h1 : n = m) (h2 : 0 < n) : (0 < m) :=
eq.subst h1 h2

theorem nowrk (h3 : n = 0) (h4 : 0 < n) : (0 < 0) :=
    by rw h3 at h4; assumption


--lemma subst_zero_ineq (h3 : n = 0) (h4 : 0 < n) : (0 < 0) :=
--    eq.subst h3 h4

--lemma subst_zero_ineq2 (h3 : 0 = n) (h4 : 0 < n) : (0 < 0) :=
--    eq.subst h3 h4


def elim_left2 (a b : Prop) (and' : and a b) : a :=
    and.rec_on and' (λ α β, α)

def elim_left: Π (a b : Prop) (and': and a b), a :=
    λ (a : Prop) (b : Prop) (and' : and a b),
    and.rec_on and' (λ α β, α)

variables a b : Prop
variable (and' : and a b)

#check @and.rec_on a b a (and')

theorem nowrk5 (h3 : n = 0) (h4 : 0 < n) : (0 < 0) :=
calc 0 < n : h4
   ... = 0 : h3


#print nat.decidable_lt

example : (0 : nat) < (3) := of_as_true trivial


