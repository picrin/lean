inductive natlist : Type
    | nil : natlist
    | cons : nat → natlist → natlist

definition list_sum : natlist → nat :=
    λ list : natlist,
    natlist.rec_on list 0 (λ list_element : nat, λ previous_list : natlist, λ IH: nat, list_element + IH)

open natlist

#reduce list_sum $ cons 2 $ cons 2 nil

#eval list_sum $ cons 4 $ cons 3 $ cons 2 nil