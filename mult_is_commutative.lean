
def multiplication : nat → nat → nat :=
    λ (a b : nat), 
    nat.rec_on a 0 (λ k result_k : nat, result_k + b)


def tricky_bastard (k b : nat) : multiplication b (nat.succ k) = multiplication b k + b :=
    nat.rec_on b rfl (
        λ (a : ℕ), λ H: multiplication a (nat.succ k) = multiplication a k + a, 
        show multiplication (nat.succ a) (nat.succ k) = multiplication (nat.succ a) k + nat.succ a, from
        have A : multiplication (nat.succ a) (nat.succ k) = multiplication a (nat.succ k) + nat.succ k, from rfl,
        have B : multiplication a (nat.succ k) + nat.succ k = multiplication a k + a + nat.succ k, from eq.subst H A,
        have C : k + 1 = 1 + k, from add_comm k 1,
        have F : a + (1 + k) = (a + 1) + k, from eq.symm (add_assoc a 1 k),
        have I : multiplication a k + (a + (k + 1)) = multiplication a k + (a + (1 + k)), from eq.subst C rfl,
        have K : multiplication a k + (a + (1 + k)) = multiplication a k + ((a + 1) + k), from eq.subst F rfl,
        have useful : multiplication a k + (a + (k + 1)) = multiplication a k + ((a + 1) + k), from eq.trans I K,
        have magic : (multiplication a k + a) + nat.succ k = multiplication a k + (a + (k + 1)), from add_assoc (multiplication a k) a (nat.succ k),
        have J : multiplication a k + (a + (k + 1)) = multiplication a k + ((a + 1) + k), from eq.trans I K,
        have M : multiplication a k + (nat.succ a + k) = multiplication a k + (k + nat.succ a), from eq.subst (add_comm (nat.succ a) k) rfl,
        have N : multiplication a k + (k + nat.succ a) = (multiplication a k + k) + nat.succ a, from eq.symm (add_assoc (multiplication a k) (k) (nat.succ a)),
        have O : (multiplication a k + k) + nat.succ a = multiplication (nat.succ a) k + nat.succ a, from rfl,
        have R : multiplication a k + a + nat.succ k = multiplication (nat.succ a) k + nat.succ a, from eq.trans (eq.trans (eq.trans (eq.trans magic J) M) N) O,
        eq.trans (eq.trans A B) R
        )


def mul_is_comm (a b : nat) : multiplication a b = multiplication b a := 
    nat.rec_on a
    (have LHS : multiplication 0 b = 0,
        from rfl,
        have RHS : multiplication b 0 = 0,
        from nat.rec_on b rfl (
        λ (k : nat), λ H : multiplication k 0 = 0, have A : multiplication (nat.succ k) 0 = multiplication k 0 + 0, from rfl, have B : multiplication k 0 + 0 = 0, from eq.subst A H, eq.trans A B),
        eq.trans LHS (eq.symm RHS))
    (λ k : nat, λ H : multiplication k b = multiplication b k,
        show multiplication (nat.succ k) b = multiplication b (nat.succ k), from
        have A : multiplication (nat.succ k) b = multiplication k b + b, from rfl,
        have B : multiplication b (nat.succ k) = multiplication b k + b, from tricky_bastard k b,
        have C : multiplication k b + b = multiplication b k + b, from eq.subst H rfl,
        eq.trans (eq.trans A C) (eq.symm B))