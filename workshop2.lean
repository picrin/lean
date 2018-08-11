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

-- Again, just like the idea of naming parameters in type signatures, "values as types" is pretty much useless on its own. We need two more ideas to even begin talking about the goal of the tutorial. The first idea is called "inductive types". But let's not talk about those until later on in the tutorial. The second idea is called "propositions as types", and it's the "thought experiment" I've alluded to in the introduction to this tutorial, and that's how it all fits together. We're going to look at it in detail in the next section.

-- Propositions as types

-- In order to do mathematics in lean we will need a special type, called `Prop`. You can think of it like `nat`, but instead of numbers, this type represents propositions, i.e. statements to which we can assign truth judgments. Examples of propositions are "3 is an even number" (untrue), "Mandy ate icecream last Friday" (we have to ask Mandy!) or "Sam knows the definition of a tensor" (true).

-- If p is any proposition, `p : Prop`, we are going to say that the proof of `p` will be any value of type `p`, `proof_of_p : p`. It's really that simple. We can begin with something relatively easy. We are going to assume that when Mandy has ice-cream, she eats it. Further, we will assume that when Mandy eats ice cream she is happy. We will produce a mathematical proof of Mandy's happiness given her pocession of icecream. Let's see!

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

-- As you can see there's a lot of clutter in the above example. Lots of variable names are unnecessarily repeated, specifically because we're using the "named parameters" trick. Lean provides us with ways to make things look better. One way is through variables. Specifically

variable (Mandy_has_icecream : Prop)
variable (Mandy_eats_icecream : Prop)
variable (Mandy_is_happy : Prop)
variable (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
variable (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy)

def Mandy_and_icecream2 : Mandy_has_icecream → Mandy_is_happy :=
    λ ice_cream_evidence : Mandy_has_icecream,
        sorry

-- Another is through moving the colon after the function name all the way to the right, like this:

def Mandy_and_icecream3 (Mandy_has_icecream : Prop)
                        (Mandy_eats_icecream : Prop)
                        (Mandy_is_happy : Prop)
                        (Mandy_rule_1 : Mandy_has_icecream → Mandy_eats_icecream)
                        (Mandy_rule_2 : Mandy_eats_icecream → Mandy_is_happy) :
                        Mandy_has_icecream → Mandy_is_happy :=
    λ ice_cream_evidence : Mandy_has_icecream,
        sorry

#check ((λ (a b : Prop), λ Pa : a, λ Pb : b, and.intro Pa Pb) : (∀ a b : Prop, a → b → a ∧ b))