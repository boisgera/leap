/-
Functions
================================================================================


Definition and Application
--------------------------------------------------------------------------------

Lets define a function named `x2` (for "times two"):
-/

def x2 (n : Nat) : Nat := 2 * n


/-
Its has one argument of type `Nat` named `n`, its result if of type `n` whose
expression is `2 * n`.
-/


/-
To use it we **apply** this function to the argument 2
-/

#eval x2 2
-- 4

/-
Note that there is no parentheses here. You can use them (if you use a space
between the function and its argument), but they would only be useful to
delimit the expression that defines the argument and it is not a part of
function application per se.
-/

#eval x2 (1 + 1)
-- 4

/-
You can also use parentheses *around* the function application expression
to make the operations precedence explicit:

-/

#eval (x2 1) + (x2 1)
-- 4

/-
We can get verify that Lean got the right type of `x2` with `#check`:
-/

#check x2
-- x2 (n : Nat) : Nat

/-
Lean is statically typed: it needs to know what the type of every
function argument and of its result are otherwise it won't **type check**
(validate) your code.
That does not mean that you always have to specify everything;
you can often be implicit about some type information and let
Lean is smart **infer** automatically the missing information:
-/

def x2' (n : Nat) := 2 * n

#check x2'
-- x2' (n : Nat) : Nat

/-
Printing `x2` gives us the type and the implementation of the function.
-/

#print x2
-- def x2 : Nat → Nat :=
-- fun n => 2 * n

/-
The expression `Nat -> Nat` denotes the type of (pure) functions with an
argument of type `Nat` and result of type `Nat`. We could also have
defined our function as:
-/

def x2'' : Nat -> Nat := fun n => 2 * n

#check x2''
-- x2'' : Nat → Nat

/-
There are very little differences between the function signatures
`x2 (n : Nat) : Nat` and `x2'' : Nat -> Nat`.
In the first case, the argument of the function has
a name that we can use when we apply the function:
-/

#check x2 (n := 2)
-- 4

/-
That won't work for `x2''`:
-/

#check x2'' (n := 2) -- ❌
-- Invalid argument name `n` for function `x2''`

/-
The `fun` keyword and `=>` symbol define an anonymous function.
For short anonymous function like that there are syntactic shortcuts;
using parentheses `()` and a centered dot (`·`, type `\` then `.`
then a space to obtain this symbol), we can also do:
-/

def x2''' : Nat -> Nat := (2 * ·)

/-
Note to apply a function, you don't need it to a name it!
any expression that evaluates to a function can work;
that's the beauty of referential transparency.
For example:
-/

#eval (fun n => 2 * n) 2
-- 4

#eval (· * 2) 2
-- 4

/-

Currying
--------------------------------------------------------------------------------

Functions can have an arbitrary number of arguments.
For example:
-/

def add (m : Nat) (n : Nat) : Nat :=
  m + n

#check add
-- add (m n : Nat) : Nat

/-
This `#check` also teaches us that given that the two function arguments have
the same type, we could have used a single set of parentheses:
-/

def add' (m n : Nat) : Nat :=
  m + n

/-
Printing the function is also informative:
-/

#print add
-- def add : Nat → Nat → Nat :=
-- fun m n => m + n

/-
The implementation printed out is not surprising; we just discovered the
notation for an anonymous function expression with two arguments.
But the `Nat -> Nat -> Nat` probably need more explanation.

The only hint you probably need: you should read it as `Nat -> (Nat -> Nat)`
(in other words: `->` is right-associative.)
That means that Lean tells you that `add` is a function with a `Nat` argument
and result ... a function with a `Nat` argument and `Nat` result!
Which makes sense: if you specify one (the first) argument of the function,
what you have left is the function of one (the second) argument!
This process (transforming a function of multiple argument into a
sequence of function of one argument) is called **currying**.

Let's check that all that makes sense:
-/

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

/-
Now remember that you need need to name functions to apply them.
Which means that the last eval could have been written as
-/

#eval (add 1) 2
-- 3

/-
The final touch: define the "space operator" in function application to
be left associative and you can get away with simply:
-/

#eval add 1 2
-- 3

/-

**TODO.** Partial application in Python.

-/

/-
### No argument

Note that given the logic of currying, by consistency, you can consider
functions without arguments even if it's a little contrived!. You won't
usually call them functions though:

-/

def two := 2

/-

This point of view is not a totally useless.
When in Python you would define a function `roll_die` to get a random number
between 1 and 6

```python
import random

def roll_die():
    return random.randint(1, 6)

print(roll_die())
# 4
```

in Lean, you would consider the constant of type `IO Nat`, which is not
a function!

-/

def rollDie : IO Nat := IO.rand 1 6

#eval rollDie
-- 6

/-
And indeed `rollDie` needs no extra information to be defined, that wouldn't
make sense to define it as a function.

There is another idiom to define that kind of object, but really as Lean functions
this time. You parametrize them with an argument in the `Unit` type. Since there
is a single element in `Unit` (the unit, denoted `()`), having such an argument
provides no information. For example:
-/

def rollDie' : Unit -> IO Nat := fun _ => IO.rand 1 6

#eval rollDie' ()
-- 5

/-
This pattern can be used to delay computations in Lean when needed.
For example if I wanted to define an `or'` function in Lean like that:
-/

def or' (x y : Bool) : Bool :=
  if y == false && x == false then
    false
  else
    true

/-
it would mostly work as expected:
-/

#eval or' false false
-- true
#eval or' false true
-- true
#eval or' true false
-- true
#eval or' true true
-- false

/-
"Mostly" because we tend to expect a short-circuit property of this operator:
if the first argument evaluates to `true`, we know that the output should be
`true` and we don't need to evaluate the second argument. And we don't want
this second argument not to be evaluated if it's not needed, since it can
require more computations. But in the current implementation, our `or'`
function doesn't work like that because Lean is *eager*, not *lazy*: it
will evaluate all the arguments to a function before starting to evaluate
the function itself.
-/

def true' :=
  dbg_trace "true'"
  true

def false' :=
  dbg_trace "false'"
  false

#eval or' (dbg_trace "#1"; true) (dbg_trace "#2"; false)
-- #2
-- #1
-- true

/-
On the other hand, if you want to be sure that the second argument will be
evaluated only when it's necessary, you can change the function signature
and implementation like that:
-/

def or'' (x : Bool) (y : Unit -> Bool) : Bool :=
  if x == true then
    true
  else
    y ()

#eval or'' (dbg_trace "#1"; true) (fun _ => dbg_trace "#2"; false)
-- #1
-- true

/-
Namespaces and Methods
--------------------------------------------------------------------------------

**TODO:**

  - Understand the rule wrt the order of arguments. I though that it was the
    first, but List.filter avoids that (???). Because p is defined on the
    left of ":" ??? Dunno. Nah, it's because what is substituted is the
    first argument that matches the type of the item on the left of .
    And therefore, stuff like filter satisfy the classic FP order *and*
    work as methods, in a more OO style


-/

/-
Composition & Piping
--------------------------------------------------------------------------------

**TODO:**

  - perentheses are a pain

  - composition somehow better, but reads right-to-left

  - |>

  - methods binding : "|>. "

-/

/-

Higher-order programming
--------------------------------------------------------------------------------

Functions can also be used as arguments to functions.

-/

def isOdd (n : Nat) : Bool :=
  n % 2 == 1

#eval [0, 1, 2, 3, 4, 5].filter isOdd
-- [1, 3, 5]

#eval [0, 1, 2, 3, 4, 5].filter fun n => n % 2 == 1
-- [1, 3, 5]

#eval [0, 1, 2, 3, 4, 5].filter (· % 2 == 1)

def threeTimesPlusOne (n : Nat) : Nat :=
    3 * n + 1

#eval [1, 3, 5].map threeTimesPlusOne
-- [4, 10, 16]

#eval [0, 1, 2, 3, 4, 5] |>.filter isOdd |>.map (3 * · + 1)
-- [4, 10, 16]

/-
In Python, the idiomatic equivalent would use a **list comprehension**:

```pycon
>>> def is_odd(n: int) -> bool:
...     return n % 2 == 1
...
>>> [3 * n + 1 for n in [0, 1, 2, 3, 4, 5] if is_odd(n)]
[4, 10, 16]
```

-/


/-
TODO:

  - local variables: let (for values and functions ...).
    Scope ("after" the decl and "limited to the block")

  - functions are first-class values / HOP patterns. Examples:
    map, filter, fold (?). Yes.

  - functions and methods / namespaces

  - Bells and whistles: (collapsed) pattern matching

  - Bells and whistles: named arguments, default arguments, etc.

  - Bells and whistles: function composition, infix notation, etc.

  - Bells and whistles: currying, partial application, etc.

  - genericity, type arguments, implicit arguments, universe arguments, etc.

  - notation for type classes use?

  -  callables: coerce your types to functions

  - Unit -> ... (lazy eval; example with lazyOr, use dbg_trace to prove)
    and ... -> Unit (...useless, but ... -> IO Unit is not)

  - recursive functions, terminal and non-terminal recursion,
    mutual recursive definitions, total/partial functions,
    termination, etc.

-/
