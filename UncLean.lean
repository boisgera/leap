/-
UncLean
================================================================================

-/

import Python

/-

✨ Embrace impurity
--------------------------------------------------------------------------------

In programming, functions can take inputs, process them and
return otuputs. But they can also have various kind of side-effects:
print messages in you terminal, send e-mails, search the Internet ...
even order lunch!

![The Enunciation Apocalypse]

[The Enunciation Apocalypse]: https://scontent-cdg4-3.xx.fbcdn.net/v/t39.30808-6/532953901_24490135003936932_7732910830382145601_n.jpg?_nc_cat=110&ccb=1-7&_nc_sid=aa7b47&_nc_ohc=qjzUJrpukJYQ7kNvwFyHj2L&_nc_oc=AdluCJNAJctXdZR9pSI6o8UviHpup3a8cBaudmzpIp5UrLly8vwdyhOj37x-lpcAuAI&_nc_zt=23&_nc_ht=scontent-cdg4-3.xx&_nc_gid=_6IzYZREoGtgmSuKScPszA&oh=00_AfWoe-jWnl7kXSuU5NDTSQjnETbPMptTujsfGxe1OWvhOw&oe=68ABE55A

In this respect they differ from mathematical functions that do not interact with the outside world and will always give the same outputs for the same inputs; such functions are **pure**. These are very strong guarantees and the core of Lean is made to manage only such functions.

Functions with potential side-effects – **impure** functions --
are carefully tracked by the Lean type system; their execution
depends on a small Lean runtime that specifically interacts with the external world.

The trick is: as long as you don't execute them, you can deal with impure functions as if they were pure, using only Lean core. And you will get all the guarantees that Lean core provides!
You simply need to "box" them into "actions" in the `IO` "context"; the choice of the `IO` context here determines the action permissions or "capabilities".

### 👋 Hello world!

Consider the `IO.println` function which prints any Lean value
(as long as it is representable as a `String`)

-/

#eval IO.println "Hello world! 👋"
-- Hello world! 👋

/-
Its signature (when we restrict it to inputs of type `String`) is:
-/

#check IO.println (α := String)
-- IO.println : String → IO Unit


/-
It is a function that accepts strings and returns outputs of type `IO Unit`.
A value of type `IO α` is an action that can be executed to yield some side-effects and return a value of type `α`.
Here `Unit` is a type that has a single value, the unit, denoted `()`.
The unit `()` is the Lean equivalent of `None` in Python
(and `Unit` is the equivalent of `NoneType`, which is `type(None)`).

Therefore, `hello` which is defined by
-/

def hello := IO.println "Hello world! 👋"

#check hello
-- hello : IO Unit

/-
is an action that when it's executed, will have a side-effect (print "Hello world! 👋") and return nothing of interest (the unit).
Now, you can ask `#eval` – who has access to Lean runtime – to execute this action:
-/

#eval hello
-- Hello world! 👋


/-
If instead of programming in the playground you want to create a program,
create a file `Hello.lean` whose contents are:
-/

def hello' := IO.println "Hello world! 👋"

def main := hello'

/-
A `main` constant with type `IO Unit` is the program entry point:
the action that Lean runtime will execute when you run the program:

```bash
$ lean --run Hello.lean
Hello world! 👋
```
-/

/-
### 🎲 Random functions

Let's now try to generate (pseudo-)random numbers with Lean.
There is in the standard library a function `IO.rand` which
can produce random natural numbers in a given range.
Its signature is:
-/

#check IO.rand
-- IO.rand (lo hi : Nat) : BaseIO Nat

/-
`BaseIO` is a context similar to `IO` but more restricted: actions in
this context are not allowed to throw exceptions. This is largely irrelevant
for us right now, since Lean will hapilly convert it to an `IO` context when it's needed.

To define that function that generates a random number between 1 and 6, you can define

-/

def rollDie := IO.rand 1 6

#check rollDie
-- rollDie : BaseIO Nat

/-
Using it several times yields something like:
-/

#eval rollDie
-- 1
#eval rollDie
-- 4
#eval rollDie
-- 6

/-
Consider a moment what you can do with a similar but pure value.
Its signature would be:
-/

def rollDieWithoutIO : Nat :=
  sorry -- No implementation yet

#check rollDieWithoutIO
-- rollDieWithoutIO: Nat

/-
Thus you **can** select a "random" number between 1 and 6, but
you'd better select it carefully because it's the only one you'll ever get!

If you pick 3 for example
-/

def rollDieWithoutIO' : Nat := 3

/-
then you will get
-/

#eval rollDieWithoutIO'
-- 3
#eval rollDieWithoutIO'
-- 3
#eval rollDieWithoutIO'
-- 3


/-
There are actually some ways to deal with (pseudo-)random numbers without `IO`,
but they require a different interface.
-/

/-
▶️ Let's `do` this
--------------------------------------------------------------------------------

### 🧩 Solving the puzzle

We are now faced with two issues:

  1. Since the core of Lean is pure and it's pretty handy, how do
    we mix pure and impure?

  2. How do we chain impure functions to define more complex impure functions?

First note that the answer to the first point should be
asymmetric: it should not be possible to execute impure functions from
pure ones, otherwise the careful tracking of impurity would be broken.
But we still need to integrate pure functions as impure ones. This is actually quite
easy, with a `do` block and the `return` keyword.
-/

def rollDieWithoutIO'' : Nat := 3

def rollFake : IO Nat := do
  return rollDieWithoutIO''

#eval rollFake
-- 3

/-
The `do` block also solves most of the chaining problem.
To chain actions, simply enumerate them in a do block:
-/

def rollDie' : IO Nat :=
  IO.rand 1 6

def rollDie'' : IO Nat := do
  IO.println "🎲 Rolling the die ..."
  rollDie

#eval rollDie''
-- 🎲 Rolling the die ...
-- 1

/-
Note that it would be useless but OK to write:
-/

def rollDie''' : IO Nat := do
  IO.rand 1 6

/-
since in this context, there is a single `IO` action, so nothing to
chain.

The real pickle comes if you want to chain two actions and have the
second one depend on the result of the first.
For example, that's the situation if we want our information message
to display the value of the rolled die instead. If we had a `Nat` value `die`, we could use the formatted string
construct of Lean
-/

def die : Nat := 3

#eval IO.println s!"🎲: {die}"
-- 🎲: 3

/-
But unfortunately this is not what `rollDie` generates: it
produces values of type `IO Nat` instead, so we a bit more help from Lean.
That comes in the form of a `<-` symbol! In a `IO` context and in a `do` block, you can use `<-` to extract a value of type `IO α` into a value of type `α`.

For us, that means that we can do:
-/

def rollDie_4 : IO Nat := do
  IO.rand 1 6

def rollDie_5 : IO Nat := do
  let die <- rollDie_4
  IO.println s!"🎲: {die}"
  return die

#eval rollDie_5
-- 🎲: 2
-- 2

/-
And before you ask, no, this is **not** a breach of the `IO` context!
Yes you can "breach" the `IO` context to get a pure `die`,
but since this is only allowed in an
enclosing `IO` context, you cannot turn an impure function into a pure one.
-/

/-
### 🔀 Control flow

-/

def rollDie_6 (verbose : Bool) : IO Nat := do
  let die <- IO.rand 1 6
  if verbose then
    IO.println s!"🎲: {die}"
  return die

#eval rollDie_6 (verbose := false)
-- 3

#eval rollDie_6 (verbose := true)
-- 🎲: 2
-- 2

/-
The `if` branch without the corresponding `else` is valid here only
because the expression `IO.println s!"🎲: {die}"` is of type `IO Unit`.
This is actually equivalent to:
-/

def pass : IO Unit := do
  return

def rollDie_7 (verbose : Bool) : IO Nat := do
  let die <- IO.rand 1 6
  if verbose then
    IO.println s!"🎲: {die}"
  else
    pass
  return die

#eval rollDie_7 (verbose := false)
-- 3

#eval rollDie_7 (verbose := true)
-- 🎲: 2
-- 2

/-
For any other type `IO α`, you will need to specify explicitly the else branch:
-/


def greeting (use_emoji : Bool): IO String := do
  if use_emoji then
    return "Hello! 👋"
  else
    return "Hello!"

#eval greeting (use_emoji := false)
-- "Hello"

#eval greeting (use_emoji := true)
-- "Hello! 👋"

/-
Lean variables are immutable by default; once declared and assigned a value,
you cannot change your mind:
-/

def print_number : IO Unit := do
  let number := 1
  number := 2 -- ❌ `number` cannot be mutated
  IO.println number

/-
but within in a `do` block, you can declare them explicitly as mutable:
-/

def print_number' : IO Unit := do
  let mut number := 1
  number := 2 -- ✅
  IO.println number

#eval print_number'
--2

/-
Mutable variables are handy in loops, which are also available in `do`
blocks. For example:
-/

def roll3d6 : IO (List Nat) := do
  let mut dices := []
  for _ in [0:3] do
    let die <- IO.rand 1 6
    dices := dices ++ [die]
  return dices

#eval roll3d6
-- [3, 3, 1]

/-
You can iterate on ranges like `[1:3]`; you can also iterate on lists:
-/

def sum3d6 : IO Nat := do
  let dices <- roll3d6
  let mut sum := 0
  for die in dices do
    sum := sum + die
  return sum

#eval sum3d6
-- 10


/-
Note that there is a handy shortcut to avoid the creation of an extra variables
that extract a value from a `IO` context when this value is only used once:
-/

def sum3d6' : IO Nat := do
  let mut sum := 0
  for die in (<- roll3d6) do
    sum := sum + die
  return sum

#eval sum3d6'
-- 10

/-
There are also `while` and `repeat` loops and `break` and `continue` statements
as well:
-/

def rollUntil (n : Nat) : IO (List Nat) := do
    let rollDie := IO.rand 1 6
    let mut dices := []
    repeat
      let die <- rollDie
      dices := dices ++ [die]
      if die == n then
        break
    return dices

#eval rollUntil 1
-- [6, 2, 4, 4, 2, 6, 2, 5, 1]

def rollUntil3x1 : IO (List Nat) := do
    let rollDie := IO.rand 1 6
    let mut dices := []
    let mut count := 0
    while count < 3 do
      let die <- rollDie
      dices := dices ++ [die]
      if die == 1 then
        count := count + 1
      else
        count := 0 -- reset
    return dices

#eval rollUntil3x1
-- [2, 4, 3, 5, 3, 6, 2, 1, 1, 5, ... , 1, 4, 4, 2, 2, 1, 3, 5, 1, 1, 1]

/-
### 🔧 Imperative style and purity

The imperative style of programming, with sequences of statements
that change of the value of mutable variables and whose execution is
are controlled by branches and loops,
can be beneficial even if you don't need the `IO` context and
your function is actually pure.

If at the moment you don't fancy the classical functional programming style

-/

def sum : List Nat → Nat
| []      => 0
| x :: xs => x + sum xs

#eval sum [1, 1, 2, 3, 5, 8, 13, 21]
-- 54

/-
or even
-/

def sum' (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + x) 0

#eval sum' [1, 1, 2, 3, 5, 8, 13, 21]
-- 54

/-
then use the `Id` context instead of `IO` which will also allow you to use
do blocks and the associated constructs:
-/

def sum'' (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

#eval sum'' [1, 1, 2, 3, 5, 8, 13, 21]
-- 54

/-
Contrarily to `IO`, computations in the `Id` context are "runnable" and thus
we can extract the final value of their computation without interaction with
the IO runtime. But they can't print message, send e-mails ... or order lunch!
-/

/-
🖤 Live and let die
--------------------------------------------------------------------------------

While there are many elaborate methods to deal with errors in Lean, I advise
you to start handling your potential errors with `panic!` which stops the program and display an error message. Functions from the standard Lean library that
handle errors this way are flagged with a `!`, use these variants until you
know better.
-/

def xs : List Nat := [1, 1, 2, 3, 5, 8, 13, 21]

def get (k : Nat) : Nat := xs[k]!

#eval get 7
-- 21

#eval get 8
-- PANIC at List.get!Internal Init.GetElem:...

/-
If you want a more friendly error message:
-/


def xs' : List Nat := [1, 1, 2, 3, 5, 8, 13, 21]

def get' (k : Nat) : Nat :=
  if k < xs'.length then
    xs'[k]!
  else
    panic s!"out of bounds: index {k} >= list length {xs'.length}"

#eval get 7
-- 21

#eval get 8
-- out of bounds: index 8 >= list length 8 ...

/-
🐍 Use Python
--------------------------------------------------------------------------------

Lean has a very limited standard library.
In this respect, that's the complete opposite of Python, which comes
"batteries included"!

So when you need a functionality that Lean lacks, call Python:

To get access to functionalities not available in Lean, call Python:

  - start a [toupie] server,

  - `import Python` in your lean code, then

  - use `Python.exec!` to execute Python code

  - use `Python. eval!` to evaluate Python expressions.

### ⚠️ Warnings

  - The code is executed *server-side*;
    `Python.exec! "print('Hello world!')"`
    *will not* display a message in your Lean session.

  - The returned value is always a Lean `String`
    (even if the Python value is not).


### 🔍 Examples
-/

def main' : IO Unit := do
  let message <- Python.eval! "'Hello world!'"
  IO.println message

#eval main'
-- Hello world!

def main'' : IO Unit := do
  let sum : String <- Python.eval! "1 + 1"
  IO.println s!"1 + 1 = {sum}"

#eval main''
-- 1 + 1 = 2

/-
You can use `Python.exec!` to define Python constants and/or functions before
calling `Python.eval!`:
-/


def pythonCode := "
def sum_integers_up_to(n):
    return n * (n + 1) // 2
"

def main_3 : IO Unit := do
    Python.exec! pythonCode
    let sum : String <- Python.eval! "sum_integers_up_to(10)"
    IO.println s!"1 + 2 + ... + 10 = {sum}"

#eval main_3
-- 1 + 2 + ... + 10 = 55

/-
Convert strings that represent Python objects to native Lean types when needed:
-/

def fact (n : Nat) : IO Nat := do
  Python.exec! "import math"
  let factString <- Python.eval! s!"math.factorial({n})"
  return factString.toNat!

def binomial (n k : Nat) : IO Nat := do
  let fact_n <- fact n
  let fact_k <- fact k
  let fact_n_k <- fact (n - k)
  return fact_n / fact_k / fact_n_k

#eval binomial 6 3
-- 20

/-
Spin a toupie server with extra Python libraries when you need them;
the `requests` library is required for the next example:

```bash
uvx --with requests toupie
```

Note that Lean 4 [raw string literals]
– especially the hash mark variant –
are very handy to define Python code without worrying
about escaping backslashes and quotes.

[raw string literals]: https://lean-lang.org/doc/reference/latest//Basic-Types/Strings/#raw-string-literals
-/

def pythonCode' := r#"
import requests

URL = "https://api.chucknorris.io/jokes/random"

def get_joke():
  joke_info = requests.get(URL).json()
  return joke_info["value"]
"#

def randomJoke : IO String := do
  Python.exec! pythonCode'
  let joke <- Python.eval! "get_joke()"
  return joke

#eval do
  let joke <- randomJoke
  IO.println joke
-- "Everybody Hates Chris" was originally called "Chuck Norris Hates Chris" but
-- Chris Rock didn't want to make a series just about how he survive Chuck
-- Norris round house kicking him EVERYDAY

/-

[toupie]: https://github.com/boisgera/toupie

-/
