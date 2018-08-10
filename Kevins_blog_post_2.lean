inductive xnat : Type
| zero : xnat
| succ : xnat → xnat

inductive equality (a : xnat): xnat → Prop
    | refl : equality a

definition equality.trans: Π (a b c : xnat), Π eq1: (equality a b), Π eq2 : (equality b c), equality a c :=
    λ a b c : xnat,
    λ eq1 : (equality a b),
    λ eq2 : (equality b c),
    @equality.rec_on b (λ x, equality a x) c eq2 eq1

definition equality.symm: Π (a b : xnat), Π eq1 : (equality a b), equality b a :=
    λ a b : xnat,
    λ eq1 : (equality a b),
    -- {a : xnat} {C : xnat → Sort l} {a_1 : xnat}, equality a a_1 → C a → C a_1
    --@equality.rec_on b (equality b) b eq1 (equality.refl a)
    @equality.rec_on a (λ b, equality b a) b eq1 (equality.refl a)


definition add : xnat → xnat → xnat :=
    λ a : xnat, λ b : xnat,
        xnat.rec_on b a (λ prev_b IH : xnat, xnat.succ IH)

def succ_over_equality : Π (a b : xnat) (H : equality a b), equality (xnat.succ a) (xnat.succ b) := λ a b : xnat, λ H : equality a b,
    equality.rec_on H (equality.refl (xnat.succ a))

def xnat.add_zero_base_case : Π a: xnat, equality (add xnat.zero (xnat.succ a)) (xnat.succ (add xnat.zero a)) := λ a: xnat, equality.refl (add xnat.zero (xnat.succ a))

def xnat.add_zero_inductive_step : Π a : xnat,
    Π IH : (equality (add xnat.zero a) a),
    equality (xnat.succ (add xnat.zero a)) (xnat.succ a) := λ a: xnat,
    λ IH, succ_over_equality (add xnat.zero a) a IH

def xnat.add_zero: Π n : xnat, equality (add xnat.zero n) n := λ n,
    xnat.rec_on n
        (equality.refl xnat.zero)
        (λ a : xnat, λ IH,
        equality.trans (add xnat.zero (xnat.succ a)) (xnat.succ (add xnat.zero a)) (xnat.succ a) (xnat.add_zero_base_case a) (xnat.add_zero_inductive_step a IH))

def xnat.add_succ (a b  : xnat) : equality (add a (xnat.succ b)) (xnat.succ (add a b)) := equality.refl (add a (xnat.succ b))

-- This is getting out of hand, we really need tactics.
def xnat.add_assoc (a b c : xnat) : equality (add (add a b) c) (add a (add b c)) :=
    xnat.rec_on c (equality.refl (add a b)) (λ prev_c : xnat, λ IH : equality (add (add a b) prev_c) (add a (add b prev_c)),
        show equality (add (add a b) (xnat.succ prev_c)) (add a (add b (xnat.succ prev_c))), from
        have H1 : equality (add b (xnat.succ prev_c)) (xnat.succ (add b prev_c)), from xnat.add_succ b prev_c,
        have H2 : equality (xnat.succ (add b prev_c)) (add b (xnat.succ prev_c)), from equality.symm (add b (xnat.succ prev_c)) (xnat.succ (add b prev_c)) H1,
        have IH_up : equality (xnat.succ (add (add a b) prev_c)) (xnat.succ (add a (add b prev_c))), from succ_over_equality (add (add a b) prev_c) (add a (add b prev_c)) IH,
        sorry)

--variables a b : xnat
--variable IH : equality (add xnat.zero a) a

--#check (equality a) b
--#check equality.refl xnat.zero
--#check xnat.zero