-- Recall that our original motivation is proving that `a + b = b + a`. Let's think about this for a moment. Technically, it would seem we've already got all the required ingeredients to make progress on this task. We know about `eq` or `=`. We know that `a` and `b` are of type `nat`. We know about `+`. However, it turns out that in order to prove `a + b = b + a`, we have to deepen our understanding of both `nat` and `+`. It turns out that `nat`, unlike corresponding concepts in other programming languages, is not primitive, i.e. it is defined in Lean using more fundamental concepts (specifically, inductive types). Let's roll our own `nat`, and to avoid name clashing, let's call it `natural`.


inductive natural : Type 
    | zero : natural
    | succ : natural → natural

-- What this definition is telling us, is that all natural numbers are of two kinds. One kind is `zero` (boring, but important!). The other kind is successors (`succ`s), i.e. natural numbers which immediately follow another natural number (e.g. 4 or 42). Every natural number is of one kind or the other, and all natural numbers belong to one of the kinds. Whenever we introduce a new definition (e.g. addition), or try to construct a new proof (e.g. `a + b = b + a`), we will have to think about both kinds, `zero` and `succ`.

-- But we can already use this definition to see something somewhat useful. We can construct any number we want, given sufficient patience. e.g. this is how we can construct 3:


#check natural.succ (natural.succ (natural.succ natural.zero))

-- Can you construct 2 and 4?

-- your code goes here.

-- Let's define addition now. We will have to use an important "magic" ingredient of inductive types: recursors. These are automatically generated for any inductive type, and are part of low-level machinery, which makes lean lean. We can use `natural.rec_on x` to prove or define things about `x`, as long as we're willing to assume that `x` can be either of a `zero` kind or of a `succ` kind. This is one good way to start defining addition:

def addition_sorry_sorry (a : natural) (b : natural) : natural :=
    natural.rec_on b sorry sorry

-- What's happening there is we're saying that we'll define addition by considering two separate cases, first case is when b is `zero`, and second case is when b is a `succ` of some other natural. In the first case things are really easy, if b is zero, the result of addition is simply `a`.

def addition_sorry (a : natural) (b : natural) : natural :=
    natural.rec_on b a sorry

-- Getting rid of the second sorry is harder. What can be of some help is replacing it with `_` and hovering over it with your pointer. This will tell you that you have to replace the unerscore with a function typed `natural → natural → natural`. What it doesn't tell you is what each of the arguments into the function are going to be. The first argument is going to, effectively `b - 1`. This is OK, because we've dealt with `zero` in the first sorry, and now we can safely assume that `b` was constructed with a `succ`, and can be looked at as `natural.succ prev_b`. The second argument is a bit more magic. It's called the "inductive hypothesis", and it's the result of feeding `prev_b` into our definition. Let's call it `result_on_prev_b`. From here it's not hard to work out that what our definition needs to return is `natural.succ result_on_prev_b`. Can you put all these details together into a working implementation of `addition`?

def addition (a : natural) (b : natural) : natural :=
    natural.rec_on b a sorry

def addition_solution (a : natural) (b : natural) : natural :=
    natural.rec_on b a (λ (prev_b : natural) (result_on_prev_b : natural), natural.succ result_on_prev_b)


-- set_option pp.all true
-- #check addition 

-- Can you think of using `#reduce` to verify the correctness of your definition? Think about testing some simple things, such as 2 + 1.

#reduce addition (natural.succ (natural.succ natural.zero)) (natural.succ natural.zero)

-- There is exactly one more good way to define addition (at least as far as I can tell!). This is to recurse on the first argument. Can you finish this definition and test that it works as expected using #reduce

def addition2 (a : natural) (b : natural) : natural :=
    natural.rec_on a sorry sorry

-- The good news is that all these definitions are already provided in lean, together with some syntactic sugar, such as allowing us to type `a + b` instead of `addition a b`, and use actual Hindu-Arabic numerals as opposed to chains of `succ`s, so for the rest of the tutorial we can just revert back to the good old `nat`.

-- We can repeat our experiment with addition and `#reduce`, this time using more human-friendly notation. What is the most important observation you can take from this experiment?

#reduce 2 + 0
#reduce 0 + 2

-- There is a standard way to prove that two terms which reduce to the same term are equal. Can you find it yourself? This place might be helfpul: https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html#equality. Can you finish off the following proof?

def two_plus_zero_equals_zero_plus_two : 2 + 0 = 0 + 2 := sorry

def two_plus_zero_equals_zero_plus_two_solution : 2 + 0 = 0 + 2 := rfl

-- Can you state the goal (to prove that a + b = b + a) of the tutorial in lean? You can call it `addition_is_commutative`. You won't be able to prove it just now, so use sorry in place of the function definition.

-- Your code goes here.

-- Introduce have 

-- Introduce chaining trans's and symm's

def add_zero_right (a : nat) : a + 0 = a :=
    rfl

def succ_over_equality {a b : nat} (H : a = b) : (nat.succ a) = (nat.succ b) :=
    eq.rec_on H (eq.refl (nat.succ a))

def add_zero_left (a : nat) : 0 + a = a :=
    nat.rec_on a rfl (λ prev_a : nat, λ IH : 0 + prev_a = prev_a,
        have X : nat.succ (0 + prev_a) = (nat.succ prev_a), from succ_over_equality IH,
        have Y : nat.succ (0 + prev_a) = (0 + (nat.succ prev_a)), from rfl,
        eq.trans (eq.symm Y) X)

-- Can you prove that `0 + a = a + 0`, using our previous examples? Hint: the answer is a chain of `eq.symm`s and `eq.trans`es, with proofs produced from add_zero

def addition_is_commutative_base_case (a b : nat): (a + 0) = (0 + a) := eq.trans (add_zero_right a) (eq.symm (add_zero_left a))
    
def successor_over_sum (a : nat) (b : nat) : a + nat.succ b = nat.succ (a + b) := rfl

def successor_over_sum2 (a : nat) (b : nat) : (nat.succ a) + b = nat.succ (a + b) :=
    nat.rec_on b rfl (λ prev_b, λ IH : nat.succ a + prev_b = nat.succ (a + prev_b),
        show nat.succ a + nat.succ prev_b = nat.succ (a + nat.succ prev_b), from
        have X : nat.succ (nat.succ a + prev_b) = nat.succ (nat.succ (a + prev_b)), from succ_over_equality IH,
        X)

def addition_is_commutative (a b : nat) : a + b = b + a :=
    nat.rec_on b
        (addition_is_commutative_base_case a b)
        (λ prev_a, λ H : a + prev_a = prev_a + a,
        show a + nat.succ prev_a = nat.succ prev_a + a, from
        have X : a + nat.succ prev_a = nat.succ (a + prev_a), from successor_over_sum a prev_a,
        have Y : (nat.succ prev_a) + a = nat.succ (prev_a + a), from successor_over_sum2 prev_a a,
        have Z : nat.succ (a + prev_a) = nat.succ (prev_a + a), from succ_over_equality H,
        (eq.trans (eq.trans X Z) (eq.symm Y)))