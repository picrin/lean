def even : ℕ → Prop
| 0 := true
| 1 := false
| (n+2) := even n

def even2 : ℕ → Prop :=
λ n, ∃ k, n = 2 * k

inductive even3 : ℕ → Prop
| zero : even3 0
| add_two : ∀ n, even3 n → even3 (n+2)

example : even3 4 :=
even3.add_two 2 $ even3.add_two 0 even3.zero

example : ∀ n, even3 n ↔ even2 n :=
λ n,
⟨λ H, even3.rec_on H ⟨0, rfl⟩ $ λ n H ⟨k, ih⟩,
⟨k + 1, @eq.rec_on nat (2 * k) (λ z, z + 2 = 2 * (k + 1)) n ih.symm rfl⟩,
λ ⟨k, H⟩, H.symm ▸ (nat.rec_on k even3.zero $ λ n, even3.add_two (2 * n))⟩

example : ∀ n, even3 n ↔ even2 n :=
begin
intro n,
constructor,
{ intro H,
induction H with n H ih,
{ existsi 0, refl },
cases ih with k ih,
rw ih,
existsi (k+1),
refl },
intro H,
cases H with k H,
rw H,
clear H n,
induction k with k ih,
{ constructor },
constructor,
assumption
end

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

theorem distributiveForAll : (∀ (x : A), r ∨ p x) ↔ (r ∨ ∀ (x : A), p x) :=
⟨λ H, or.cases_on (classical.em r) or.inl $ λ h1,
or.inr $ λ x, or.resolve_left (H x) h1,
λ H, or.cases_on H (λ h1 x, or.inl h1) $ λ h1 x, or.inr $ h1 x⟩
