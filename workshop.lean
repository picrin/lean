-- Like almost any programming language, lean has functions. `double` for example is a function.

def double : nat → nat :=
    λ a : nat, a + a

-- `nat → nat` is the function's type signature. It means that `double` accepts a non-negative integer (we'll call those "nat") and it produces another nat.

-- It's possible to use `def` to create simpler "functions", which we really should call "constants"

def purpose_of_life : nat := 42

-- Exercise 1. Can you feed some nats into `double` and see what happens (hopefully nothing too surprising!). You'll have to use `#reduce func_name argument`

--BEGIN hide
#reduce double 2
--END hide

-- Exercise 2. Can you use `#check` to check the type signature of `double`? Is it what you've expected? What's the type signature of `double 2`

--BEGIN hide
#check double 
--END hide

-- Exercise 3. Can you make `triple_and_add` into a function, which takes two arguments, `a` and `b` and produces a sum of a triple of `a` and a `b`?

def triple_first_and_add : nat → nat → nat :=
    λ a : nat, λ b : nat, sorry

--BEGIN hide
def triple_first_and_add_solution : nat → nat → nat :=
    λ a : nat, λ b : nat, 3 * a + 3 * b
--END hide

-- If you're lazy to type λ (which you can type \lambda and press enter), you can use a shortcut like this:

def triple_first_and_add2 : nat → nat → nat :=
    λ a b : nat, sorry

--BEGIN hide
def triple_first_and_add2_solution : nat → nat → nat :=
    λ a b : nat, 3 * a + 3 * b
--END hide

-- Exercise 4. Can you check the type signature of the expression `triple_first_and_add 42`? What do you expect it to be? What do you expect it to evaluate to when evaluated with `#reduce`?

-- What does the function `double_and_double` do? Can you confirm with `#reduce`? Can you think of a different way to implement this function? 

def double_and_double : nat → nat :=
     λ a : nat, (a + a) + (a + a)

#reduce double_and_double 4

-- Exercise 5. Have you heard about function composition? Could you implement a `doubler`, a function, which takes a function, let's call it the `input_function` and produces another function, let's call it the `output_function`, which takes in an argument, passes it through the `input_function`, takes the result, and again passes it through the input function.

def doubler : (nat → nat) → (nat → nat) :=
    sorry

--BEGIN hide
def doubler_solution : (nat → nat) → (nat → nat) :=
    λ input_function : (nat → nat),
    λ argument  : nat, input_function (input_function argument)
--END hide

-- Exercise 6. Can you use your implementation of `doubler` to again implement `double_and_double`? How about `triple_and_double`?

def double_and_double_with_doubler : nat → nat:=
    sorry


def double_and_double_with_doubler_solution : nat → nat:=
    λ a : nat, doubler_solution double a

#reduce double_and_double_with_doubler_solution 2

--#check λ a : nat, λ b : nat, 3 * a + b

#reduce (λ a : nat, a + a) 5
--#reduce triple_and_add 3

--#check triple_and_add 3