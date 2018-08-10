inductive xnat
| zero : xnat
| succ : xnat → xnat

#check xnat.zero

def one := xnat.succ xnat.zero
def two := xnat.succ one

definition add : xnat → xnat → xnat :=
    λ a : xnat, λ b : xnat,
        xnat.rec_on b a (λ prev_b IH : xnat, xnat.succ IH)

notation a + b := add a b

#reduce add (xnat.succ xnat.zero) (xnat.succ (xnat.succ xnat.zero))

-- 1. Feedback on the sentence: "Here’s the full code (together with some other stuff which you don’t need to worry about)."
-- I'd probably avoid using `open` for now. Every bit of new notation introduced is a new thing to learn and can distort the "bigger picture". Sure, typing xnat before everything is a pain, but they'll have plenty of time to learn all the shortcuts as they become more expert (i.e. after the first lesson).

-- 2. Feedback on the sentence: "Well no we can’t yet, because we haven’t defined add yet! Let’s add a definition of add. We’ll define it by induction! Well, more precisely, by recursion."
-- I'd like to see some verification/testing that my definition worked straight after the definition. For example something like this:
-- #reduce add (xnat.succ xnat.zero) (xnat.succ (xnat.succ xnat.zero))

-- 3. Feedback on the sentence "Well, more precisely, by recursion. The idea is that a+0 will just be a, and a+succ(b) will just be succ(a+b)."
-- I'm not sure how I feel about equation compiler. On one hand it makes everything look easy and is probably more beginner-friendly than recursors. On the other it is hiding quite a lot of seemingly important detail. It's a tought one!

-- 4. Feedback on the sentence "notation a + b := add a b"
-- same point applies as with `open`, but less strongly.

-- 5. Feedback on the sentence: "In fact there is an easier way — the tactic refl just unravels everything and then checks that you’re left with something of the"
-- Yes, the tactic works. Arguably an easier way to kill the goal would be without entering the tactic environment alltogether, `rfl` or `eq.refl _` or `eq.refl two`. But educationally what really matters is that all these proof strategies work because both `add (xnat.succ xnat.zero) (xnat.succ xnat.zero)` and `xnat.succ (xnat.succ xnat.zero)` reduce to the same term:
-- #reduce add (xnat.succ xnat.zero) (xnat.succ xnat.zero)
-- #reduce xnat.succ (xnat.succ xnat.zero)


theorem one_add_one_equals_two : one + one = two :=
    eq.refl _

--theorem one_add_one_equals_two_two : one + one = two :=
--    begin
--    end

-- Carry on with the tactics: https://leanprover.github.io/reference/tactics.html
-- Carry on with blog post: https://xenaproject.wordpress.com/2017/10/31/building-the-non-negative-integers-from-scratch/

definition magic : add (xnat.succ xnat.zero) (xnat.succ xnat.zero) = xnat.succ (xnat.succ xnat.zero) := rfl

--#reduce add (xnat.succ xnat.zero) (xnat.succ xnat.zero)

--#reduce xnat.succ (xnat.succ xnat.zero)
--definition magic2 : add one one == two := eq.refl two

-- Feedback on sentence `theorem add_zero (n : xnat) : n + zero = n :=`
-- You're using a lot of syntactic sugar, such as `theorem`, `example`, `definition`. All of this can potentially confuse students (although your crowd is a bit more mathematically advanced than mine). I'd probably just advise them to stick with `def` for now.

lemma succ_over_equality (a b : xnat) (H : eq a b) : eq (xnat.succ a) (xnat.succ b) :=
    eq.rec_on H (eq.refl (xnat.succ a))

definition xnat.add_zero: Π n : xnat, add xnat.zero n = n := λ n, xnat.rec_on n (eq.refl xnat.zero)
(λ a : xnat, λ IH,
    have A : add xnat.zero (xnat.succ a) = xnat.succ (add xnat.zero a), from rfl,
    have B : xnat.succ (add xnat.zero a) = (xnat.succ a), from succ_over_equality (add xnat.zero a) a IH, eq.trans A B)

example: xnat.succ (xnat.succ xnat.zero) = xnat.succ (xnat.succ xnat.zero) := rfl