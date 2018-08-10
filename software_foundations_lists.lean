--variable alpha : Type
--variable a : alpha
--variable depends_on_a : alpha → Type
--variable b : depends_on_a a

--#reduce (sigma.mk a b).2

inductive natprod : Type
    | pair : nat → nat → natprod

definition first : natprod → nat :=
    λ (x : natprod),
    natprod.rec_on x (λ a b : nat, a)

definition second : natprod → nat :=
    λ (x : natprod),
    natprod.rec_on x (λ a b : nat, b)

definition swap_natprod : natprod → natprod :=
    λ (x : natprod),
    natprod.pair (second x) (first x)

inductive natlist : Type
    | nil : natlist
    | cons : nat → natlist → natlist

definition list_sum : natlist → nat :=
    λ list : natlist,
    natlist.rec_on list 0 (λ list_element : nat, λ previous_list : natlist, λ IH: nat, list_element + IH)

open natlist

#reduce list_sum $ cons 2 $ cons 2 nil

#eval list_sum $ cons 4 $ cons 3 $ cons 2 nil

definition surjective_pairing (a : nat) (b : nat) (p : natprod) : p = natprod.pair (first p) (second p) :=
    natprod.rec_on p (λ a a_1 : nat, eq.refl (natprod.pair a a_1))

definition surjective_swap (a : nat) (b : nat) (p : natprod) : swap_natprod p = natprod.pair (second p) (first p) :=
    natprod.rec_on p (λ a a_1 : nat, eq.refl (natprod.pair a_1 a))

#reduce first (natprod.pair 3 4)


--#check cons 5 $ cons 4 $ cons 3 nil

--#reduce cons 5 $ cons 4 $ cons 3 nil

--#reduce repeat 5 4