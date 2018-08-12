-- In the previous section you've seen some basic usage of lean, which revealed lean as a functional programming language, not unlike Haskell. If you end up doing Computer Science at Edinburgh, you'll get to know functional programming very well right from the beginning (in Glasgow you have to wait until the end of your degree to pick it up as an elective).

-- But let's look at what makes lean different. As you might have realised by now, you can use `#check` to see the type of an unnamed function like this

#check (λ (a : nat), a + a)

-- You can also supply Lean with your own type signature, just to verify internal consistency of your thinking:

#check ((λ (a : nat), a + a) : (nat → nat))

-- Now, the first substantial difference between lean and other functional languages is that you can give a name to the first parameter of your function in the type signautre:

#check ((λ (a : nat), a + a) : (∀ (a : nat), nat))

-- This is just a part of a bigger idea, but it's important, and we should practice it. Can you supply the following function with a correct type signature, naming each parameter? Is it legal to use other letters than `a` and `b`? You can type ∀ like this "\forall".

#check ((λ (a b : nat), 3 * a + b))

#check ((λ (a b : nat), 3 * a + b) : (∀ (a b : nat), nat))

-- So far so good. The second big idea, and the first time I saw this it blew my mind, is that values (things to the left of the colons), can in fact, in some circumstances, become types (things to the right of the colons). This idea is unfortunately more difficult to introduce than the previous idea. We can turn to a trite "animal farm" example from the world of object-oriented programming.

#check ((λ animal : Type, λ cat : animal, cat) : ∀ (animal : Type) (cat : animal), animal)

-- Can you turn my trite example into something a bit less dull? Haggis cake & ice cream both come to mind...

-- Your creative "values as types" example comes here.

-- Again, just like the idea of naming parameters in type signatures, "values as types" is pretty much useless on its own. We need two more ideas to even begin talking about the goal of the tutorial. The first idea is called "inductive types". But let's not talk about those until later on in the tutorial. The second idea is called "propositions as types", and it's the "thought experiment" I've alluded to in the introduction to this tutorial, and that's how it all fits together.

-- Propositions as types

-- In order to do mathematics in lean we will need a special type, called `Prop`. You can think of it like `nat`, but instead of numbers, this type represents propositions, i.e. statements to which we can assign truth judgments. Examples of propositions are "3 is an even number" (untrue), "Mandy ate icecream last Friday" (we have to ask Mandy!) or "Sam knows the definition of a tensor" (true).

-- If p is any proposition, `p : Prop`, we are going to say that the proof of `p` will be any value of type `p`, `proof_of_p : p`. It's really that simple! We can begin with something relatively easy. We are going to assume that when Mandy has ice-cream, she eats it. Further, we will assume that when Mandy eats ice cream she is happy. We will produce a mathematical proof of Mandy's happiness given her pocession of icecream. Let's see!

def Mandy_and_icecream : (∀ (Mandy_has_icecream : Prop)
                        (Mandy_eats_icecream : Prop)
                        (Mandy_is_happy : Prop)
                        (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
                        (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy),
                        Mandy_has_icecream → Mandy_is_happy) :=
    λ (Mandy_has_icecream
        Mandy_eats_icecream
        Mandy_is_happy : Prop)
        (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
        (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy),
        λ ice_cream_evidence : Mandy_has_icecream,
            sorry -- can you show that Mandy is happy?

def Mandy_and_icecream_solution : (∀ (Mandy_has_icecream : Prop)
                                (Mandy_eats_icecream : Prop)
                                (Mandy_is_happy : Prop)
                                (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
                                (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy),
                                Mandy_has_icecream → Mandy_is_happy) :=
    λ (Mandy_has_icecream
        Mandy_eats_icecream
        Mandy_is_happy : Prop)
        (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
        (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy),
        λ ice_cream_evidence : Mandy_has_icecream,
            Mandy_rule_2 (Mandy_rule_1 ice_cream_evidence)

-- As you can see there's a lot of clutter in the example above. Lots of variable names are unnecessarily repeated, specifically because we're using the "named parameters" trick. Unlike in some of the examples before, we must the "named parameters" trick, because otherwise we can't use the "values as types" trick, and consequently we can't encode proofs of our propositions as relevant types. However, unnecessary clutter is unnessary clutter, and Lean provides us with ways to make things look better. One way is through variables. The code below is equivalent with the code above:

variable (Mandy_has_icecream : Prop)
variable (Mandy_eats_icecream : Prop)
variable (Mandy_is_happy : Prop)
variable (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
variable (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy)

def Mandy_and_icecream2 : Mandy_has_icecream → Mandy_is_happy :=
    λ ice_cream_evidence : Mandy_has_icecream,
        sorry -- you should be able to show that Mandy is happy using exactly the same code.
        --Mandy_rule_2 (Mandy_rule_1 ice_cream_evidence)


-- A word of warning. You might be tempted to think of variables as python or C++ variables. Don't. They really are just parameters into the function `Mandy_and_ice_cream2`, and you can verify that with `#check Mandy_and_icecream2`.


-- Another method to get rid of clutter is through moving the colon after the function name all the way to the right (and removing the ∀), like this:

def Mandy_and_icecream3 (Mandy_has_icecream : Prop)
                        (Mandy_eats_icecream : Prop)
                        (Mandy_is_happy : Prop)
                        (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
                        (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy)
                        :
                        Mandy_has_icecream → Mandy_is_happy :=
    λ ice_cream_evidence : Mandy_has_icecream,
        sorry -- you should be able to show that Mandy is happy using exactly the same code.

-- There is one more example worth looking at just now, although you won't be able to fully understand it until you've studied inductive types to a level beyond this tutorial.

-- Consider for example two variables `a : nat` and `b : nat`. Lean has a special, function-like thingy (actually an inductive type), called `eq`. Can you check what is the type of `eq a b`? Given the type information, what do you think you'll be able to do with it?

variable a : nat
variable b : nat

-- Here you can check the type of `eq a b`.

variable proof_of_a_equals_b : eq a b

-- What is the type of `proof_of_a_equals_b`? Could you tell without `#check`?

-- Typing `eq a b` is not very natural. Lean provides with alternative syntax, `a = b`. Sometimes you might have to translate in your head between `eq a b` and `a = b`, but most of the time the latter is easier to work with.

variable c : nat
variable d : nat

#check eq c d
variable proof_of_c_equals_d : c = d

-- Lean provides us with a function `eq.trans`. Can you check its type signature and use it to prove that `e = g`?

def e_equals_g (e : nat) (f : nat) (g : nat) (e_equals_f : e = f) (f_equals_g : f = g) : e = g :=
    sorry

def e_equals_g_solution (e : nat) (f : nat) (g : nat) (e_equals_f : e = f) (f_equals_g : f = g) : e = g :=
    eq.trans e_equals_f f_equals_g

-- Can you come up with your own exercise using `eq.symm`? Again, you'll have to check its type signature before you start playing with it.

-- your own exercise using `eq.symm` comes here.

-- There are other interesting things you can do with `Prop`, all beyond the scope of this tutorial, but you can check out chapter 3 of "Theorem proving in lean" https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html


-- Summary.

-- In order to do maths in lean, we need the following 4 ideas:
-- "named parameters"
-- "values as types"
-- propositions as types
-- inductive types

-- In the next section we'll make a quick overview of inductive types and move straight to the final goal of this tutorial, showing that `a + b = b + a`.