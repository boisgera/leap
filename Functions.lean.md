
Functions
================================================================================

Let `timesTwo` be our first function:

```lean
def timesTwo (n : Nat) := 2 * n
```

*Function application*, is the computation of the result of the function from
its argument:

```lean
#eval timesTwo 2
-- 4
```

Note that there is no parentheses here. You can use them (if you use a space
between the function and its argument), but they would only be useful to
delimit the expression that defines the argument and not a part of function
application per se.

```lean
#eval timesTwo (1 + 1)
-- 4
```

Checking this function teaches us that Lean has correctly inferred the
type of the function result.

```lean
#check timesTwo
-- timesTwo (n : Nat) : Nat
```

Lean is statically typed and needs to know what the type of every
function argument and of its result are. If this is ambiguous, you
can always specify this return type explicitly (and it may be a good
idea to do so, even if it's not ambiguous)

```lean
def timesTwo' (n : Nat) : Nat := 2 * n
```

Printing `timesTwo` gives us the type and the implementation of the function.

```lean
#print timesTwo
-- def timesTwo : Nat → Nat :=
-- fun n => 2 * n
```

The expression `Nat -> Nat` denotes the type of (pure) functions with an
argument of type `Nat` and result of type `Nat`. We could also have
defined our function as:

```lean
def timesTwo'' : Nat -> Nat := fun n => 2 * n
```

The `fun` keyword and `=>` symbol define an anonymous function.
For short anonymous function like that there are syntactic shortcuts;
using parentheses `()` and a centered dot (`·`, type `\` then `.`
then a space to obtain this symbol), we can also do:

```lean
def timesTwo''' : Nat -> Nat := (2 * ·)
```

Note to apply a function, you don't need it to have
a name; any expression that evaluates to a function can work!
For example:

```lean
#eval (fun n => 2 * n) 2
-- 4

#eval (· * 2) 2
-- 4
```


Functions with several arguments
--------------------------------------------------------------------------------

You can consider functions with an arbitrary (but fixed) number of arguments.
For example:

```lean
def add (m : Nat) (n : Nat) : Nat :=
  m + n

#check add
-- add (m n : Nat) : Nat
```

This `#check` also teaches us that given that the two function arguments have
the same type, we could have used a single set of parentheses:

```lean
def add' (m n : Nat) : Nat :=
  m + n
```

Printing the function is also informative:

```lean
#print add
-- def add : Nat → Nat → Nat :=
-- fun m n => m + n
```

The right-hand side of `:=` is not surprising; we just discovered the
notation for an anonymous function expression with two arguments.
But the `Nat -> Nat -> Nat` probably need more explanation.

The only hint you probably need: you should read it as `Nat -> (Nat -> Nat)`.
(`->` is right-associative.)
That means that Lean tells you that `add` is a function with a `Nat` argument
and result ... a function with a `Nat` argument and `Nat` result!
Which makes sense: if you specify one (the first) argument of the function,
what you have left is the function of one (the second) argument!
This process (transforming a function of multiple argument into a
sequence of function of one argument) is called **currying**.

Let's check that all that makes sense:

```lean
#check add 1
-- add 1 : Nat -> Nat

def add_1 := add 1

#check add_1
-- add_1 (n : Nat) : Nat

#print add_1
-- def add_1 : Nat → Nat :=
-- add 1

#eval add_1 2
-- 3
```

Now remember that you need need to name functions to apply them.
Which means that the last eval could have been written as

```lean
#eval (add 1) 2
-- 3
```

The final touch: define the "space operator" in function application to
be left associative and you can get away with simply:

```lean
#eval add 1 2
-- 3
```

TODO:

  - define a function "as usual" + function application (TODO: Python first)
    nota: functions are named.

  - define a function using the anonymous function syntax (Python lambda and
    its limitations : 1 expression, no statements, etc.)

    See where the type info can be put (or inferred).

  - functions are first-class values ...

  - ... then what is there types?

  - function with >=1 arguments, what is their types? Currying,
    partial application, notation (associativity for -> and function application),
    etc.

  - functions with 0 arguments :)

  - functions as arguments, example patterns

  - callables: coerce your types to functions

  - Shortcut centered dot

  - Bells and whistles: pattern matching

  - Bells and whistles: named arguments, default arguments, etc.

  - Bells and whistles: function composition, infix notation, etc.

  - Bells and whistles: currying, partial application, etc.

  - genericity, type arguments, implicit arguments, universe arguments, etc.

  - notation for type classes use?
