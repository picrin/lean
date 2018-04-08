def my_lt_add_right: ∀ n k : nat, n <= n + k
    | n 0 := nat.le_refl n
    | n (nat.succ j) := nat.le_succ_of_le (my_lt_add_right n j) 