def even : ℕ → Prop 
| 0 := true
| 1 := false
| (n + 2) := even n

def even2 : ℕ → Prop :=
    λ n : ℕ, ∃ k : ℕ, 2 * k = n

inductive even3 : ℕ → Prop
| zero : even3 0
| add_two : ∀ d: nat, even3 d → even3 (d + 2)

lemma even2_progression (d : ℕ) : even2 d → even2 (d + 2) :=
    λ H, have step : (∀ (a : nat), (2 * a = d → even2 (d + 2))) → (even2 (d + 2)),
         from exists.elim H,
         have element : (∀ (a : nat), (2 * a = d → even2 (d + 2))), from
         (λ a, λ Pae : 2 * a = d,
            have Paep1 : 2 * (a + 1) = d + 2, from eq.subst Pae rfl,
            show even2 (d + 2), from exists.intro (a + 1) Paep1),
         step element

def even_equality : ∀ k : ℕ, even3 k → even2 k :=
    λ k H,
        even3.rec_on H
            (exists.intro 0 rfl)
            (λ d : ℕ, λ Pe3: even3 d, λ Pe2: even2 d, even2_progression d Pe2)

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ (q ∧ p) :=
    begin
        apply and.intro,
        exact hp,
        apply and.intro hq hp
    end