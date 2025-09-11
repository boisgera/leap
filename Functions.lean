/-
Functions
================================================================================


Definition and Application
--------------------------------------------------------------------------------

Let's define a function named `x2` (for "times two"):
-/

def x2 (n : Nat) : Nat := 2 * n


/-
Its has one argument of type `Nat` named `n`, its result if of type `Nat`
and its expression is `2 * n`.
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
your code.
That does not mean that you always have to specify everything;
you can often be implicit about some type information and let
Lean **infer** automatically the missing information:
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
That's interesting!
The expression `Nat -> Nat` denotes the type of functions with an
argument of type `Nat` and result of type `Nat`. We may as well have
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
Note that to apply a function, you don't need it to a name it!
Any expression that evaluates to a function can work.
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
The implementation `fun m n => m + n` is not surprising; this is the
notation for an anonymous function expression with two arguments.
But the `Nat -> Nat -> Nat` notation probably requires more explanation.

The only hint you really need: you should read it as `Nat -> (Nat -> Nat)`
(in other words: the operator `->` is **right-associative**.)
That means that Lean tells you that `add` is a function with a `Nat` argument
and result ... a function with a `Nat` argument and `Nat` result!
Which makes sense: if you specify one (the first) argument of the function,
what you have left is the function of one (the second) argument!
This process (transforming a function of multiple argument into a
sequence of function of one argument) is called **currying**.
The first step of the process is called **partial application**.

Let's check that all that makes sense in practice:
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
Now remember that you don't need to name functions to apply them.
Which means that the last eval could have been written as
-/

#eval (add 1) 2
-- 3

/-
The final touch: define the "space operator" in function application to
be **left associative** and you can get away with simply:
-/

#eval add 1 2
-- 3

/-
Python has no syntactic support for currying, but it supports partial
application with the standard library `functools`:

```pycon
>>> from functools import partial
>>> def add(m, n):
...     return m + n
...
>>> add_1 = partial(add, 1)
>>> add_1(2)
3
```

-/

/-
### No argument

Note that given the logic of currying, by consistency, you can consider
functions without arguments even if it's a little contrived! You won't
usually call them functions though:

-/

def two := 2

/-

This point of view is not completely useless when comparing Lean with Python.
When in Python you would define a function `roll_die` to get a random number
between 1 and 6 with:

```python
import random

def roll_die():
    return random.randint(1, 6)

print(roll_die())
# 4
```

in Lean, you would consider the constant of type `IO Nat`, which is not
a function, but a "value" of type `IO Nat`!

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
Function with a `Unit` argument are often used in conjunction with the
`Thunk` type to implement [lazy computations].

[lazy computations]: https://lean-lang.org/doc/reference/latest//Basic-Types/Lazy-Computations/#Thunk

To begin with, we need to realize that Lean is *eager* by default, not *lazy*:
it will evaluate the arguments of a function before evaluating the function
itself. That includes situations where we could have avoided such computations.
Consider for example:
-/

def dbg_two :=
  dbg_trace "🚩"
  2

def f (n : Nat) (use : Bool) : Nat :=
  if use then
    n
  else
    0

#eval f dbg_two (use := true)
-- 🚩
-- 0

#eval f dbg_two (use := false)
-- 🚩
-- 2

/-
In the second case, we didn't need to evaluate `dbg_two` to produce the
result of `f` but Lean did it anyway. We have a way to deal around that
if we replace the `Nat` argument with a `Unit -> Nat` function argument
that we will evaluate only when we need it:
-/

def dbg_two' : Unit -> Nat :=
  fun () =>
    dbg_trace "🚩"
    2

#check dbg_two'
-- dbg_two' : Unit → Nat

#eval dbg_two' ()
-- 🚩
-- 2

def f' (n : Unit -> Nat) (use : Bool) : Nat :=
  if use then
    n ()
  else
    0

#eval f' dbg_two' (use := false)
-- 0

#eval f' dbg_two' (use := true)
-- 🚩
-- 2

/-
It works!
The downside of this is that we add to redesign the whole thing
and the the user of `f'` now needs to remember to
use the more complex `dbg_two'` instead of `dbg_two`.
-/

/-
Fortunately, their is a way to change that with the `Thunk` type.
It's a simple wrapper around functions with a `Unit` argument:
-/

#check Thunk.mk
-- Thunk.mk.{u} {α : Type u} (fn : Unit → α) : Thunk α

def thunk := Thunk.mk dbg_two'

#eval thunk.get
-- ⌛
-- 2

/-
But a term `e` of type `α` will automatically be
[converted to the thunk](https://lean-lang.org/doc/reference/latest///Basic-Types/Lazy-Computations/#Thunk-coercions)
`Thunk.mk fun () => e : Thunk α` when needed,
and that delays the evaluation of the original term `e`.
In action, this fact allows use to get the benefit of lazy computation
with the ease of use of our original API:

-/

def f'' (n : Thunk Nat) (use : Bool) : Nat :=
  if use then
    n.get
  else
    0

#eval f'' dbg_two (use := false)
-- 0

#eval f'' dbg_two (use := true)
-- ⌛
-- 2


/-
Namespaces and Methods
--------------------------------------------------------------------------------

Consider the function `List.replicate`:
-/


#check List.replicate
-- List.replicate.{u} {α : Type u} (n : Nat) (a : α) : List α

/-
It's a function in the namespace `List`; it can be applied like every function:
-/

#eval List.replicate 3 0
-- [0, 0, 0]

/-
The case of the function `List.append` is similar:
-/

#check List.append
-- List.append.{u} {α : Type u} (xs ys : List α) : List α

#eval List.append [1, 2, 3] [4, 5, 6]
-- [1, 2, 3, 4, 5, 6]

/-
However here we can also use the method syntax to apply it:
-/

#eval [1, 2, 3].append [4, 5, 6]
-- [1, 2, 3, 4, 5, 6]

/-
Lean with search among the function arguments the first one whose type
matches the namespace in which the function is declared (here `List`)
and use the expression at the left of the point for this argument.
-/

/-
The first match doesn't have to be the first argument.
For example:
-/

#check List.map
-- List.map.{u, v} {α : Type u} {β : Type v} (f : α → β) (l : List α) : List β

#eval List.map (· + 1) [0, 1, 2]
-- [1, 2, 3]

#eval [0, 1, 2].map (· + 1)


/-
Note that all namespaces are open: you can add a function to a namespace even
if it's associated to a built-in types. Therefore you can add any method
you like to an existing type (not that it's necessarily a good idea...).
-/

namespace String
def lolspeak (text : String) : String :=
  s!"I Can Has {text.capitalize.replace "se" "z"}?"
end String

#eval "cheeseburger".lolspeak
-- "I Can Has Cheezburger?"

/-
Alternatively, use the simpler:
-/

def String.lolspeak' (text : String) : String :=
  s!"I Can Has {text.capitalize.replace "se" "z"}?"

#eval "cheeseburger".lolspeak'
-- "I Can Has Cheezburger?"


/-
Composition & Piping
--------------------------------------------------------------------------------

Consider the following indentation function:
-/

def indent (n : Nat) (text: String) : String :=
  "\n".intercalate (
    (text.splitOn "\n").map (
      fun line =>
        (String.mk (List.replicate n ' ')) ++ line
    )
  )

#eval IO.println "aaa\nbbb\nccc"
--- aaa
--- bbb
--- ccc

#eval IO.println (indent 4 "aaa\nbbb\nccc")
---     aaa
---     bbb
---     ccc

/-
Its code is a bit hard to read but that's the point that we're addressing
here! We can make things easier for the reader by naming an intermediate
result:
-/

def indent' (n : Nat) (text: String) : String :=
  let tab := String.mk (List.replicate n ' ')
  "\n".intercalate ((text.splitOn "\n").map (tab ++ ·))

#eval IO.println (indent' 4 "aaa\nbbb\nccc")
---     aaa
---     bbb
---     ccc

/-
And since that's quite effective, we can be tempted to introduce more
variables:
-/

def indent'' (n : Nat) (text : String) : String :=
    let tab := String.mk (List.replicate n ' ')
    let splitLines := fun (text : String) => text.splitOn "\n"
    let tabulate := fun line => tab ++ line
    let joinLines := fun lines => "\n".intercalate lines
    joinLines ((splitLines text).map tabulate)

#eval IO.println (indent'' 4 "aaa\nbbb\nccc")
---     aaa
---     bbb
---     ccc

/-
Now we can make more obvious the sequence of operations that are applied to the
`text` argument if we use the composition operator `∘`:
-/

def indent''' (n : Nat) (text : String) : String :=
    let tab := String.mk (List.replicate n ' ')
    let splitLines := fun (text : String) => text.splitOn "\n"
    let tabulate := fun line => tab ++ line
    let joinLines := fun lines => "\n".intercalate lines
    (joinLines ∘ List.map tabulate ∘ splitLines) text

#eval IO.println (indent''' 4 "aaa\nbbb\nccc")
---     aaa
---     bbb
---     ccc

/-
But actually, it's a bit painful to read this last line from the right to
the left to see what's going on. Good news, instead we use the pipe operator
`|>`:
-/

def indent_4 (n : Nat) (text : String) : String :=
    let tab := String.mk (List.replicate n ' ')
    let splitLines := fun (text : String) => text.splitOn "\n"
    let tabulate := fun line => tab ++ line
    let joinLines := fun lines => "\n".intercalate lines
    text |> splitLines |>.map tabulate |> joinLines

#eval IO.println (indent_4 4 "aaa\nbbb\nccc")
---     aaa
---     bbb
---     ccc

/-
`text |> splitlines` is equivalent to `splitlines text`:
this is simply function application in disguise!
The `|>.` variant is the method pipe:
`lines |>.map tabulate` is the same as `lines.map tabulate`
or `lines |> List.map tabulate`.

These pipes operators are left-associative:
`text |> splitLines |>.map tabulate |> joinLines` should be understood
as `(((text |> splitLines) |>.map tabulate) |> joinLines)`.
-/

/-
Now it's time to reconsider our initial design; the pipes operators are so
good at their job that *maybe* you don't need to name every operation which
is applied to the data. Consider using instead:
-/
def indent_5  (n : Nat) (text : String) :=
  let tab := ' ' |> List.replicate n  |> String.mk
  text |>.splitOn "\n" |>.map (tab ++ ·) |> "\n".intercalate

#eval IO.println (indent_4 4 "aaa\nbbb\nccc")
---     aaa
---     bbb
---     ccc

/-

Higher-order programming
--------------------------------------------------------------------------------

Functions be used as arguments to other functions; they are **first-class values**.

-/

def isOdd (n : Nat) : Bool :=
  n % 2 == 1

#eval [0, 1, 2, 3, 4, 5].filter isOdd
-- [1, 3, 5]

/-
As usual, naming the function `isOdd` may help, but it's not mandatory.
You can consider using instead
-/


#eval [0, 1, 2, 3, 4, 5].filter fun n => n % 2 == 1
-- [1, 3, 5]

/-
or even
-/

#eval [0, 1, 2, 3, 4, 5].filter (· % 2 == 1)
-- [1, 3, 5]

/-
`filter` selects some items in a list, `map` apply a transform to each
element in a list:
-/

def threeTimesPlusOne (n : Nat) : Nat :=
    3 * n + 1

#eval [1, 3, 5].map threeTimesPlusOne
-- [4, 10, 16]

/-
Combine both operations with:
-/

#eval [0, 1, 2, 3, 4, 5] |>.filter isOdd |>.map (3 * · + 1)
-- [4, 10, 16]

/-
The Pythonic equivalent would be a **list comprehension**:

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

  - Bells and whistles: (collapsed) pattern matching

  - Bells and whistles: named arguments, default arguments, etc.
   type signature: Optparam stuff; see List.splitOn


  - genericity, type arguments, implicit arguments, universe arguments, etc.

  - notation for type classes use?

  -  callables: coerce your types to functions

  - recursive functions, terminal and non-terminal recursion,
    mutual recursive definitions, total/partial functions,
    termination, etc.

-/
