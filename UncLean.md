UncLean
================================================================================

✨ Embrace Purity
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
You simply need to "box" them into "actions" in the `IO` "context"; the choie of the `IO` context here determines the action permissions or "capabilities". 

### 👋 Hello world!

Consider the `IO.println` function which prints any Lean value
(as long as it is representable as a `String`)

```lean
#eval IO.println "Hello world! 👋"
-- Hello world! 👋
```
Its signature (when we restrict it to inputs of type `String`) is:

```lean
#check IO.println (α := String)
-- IO.println : String → IO Unit
```

It is a function that accepts strings and returns outputs of type `IO Unit`.
A value of type `IO α` is an action that can be executed to yield some side-effects and return a value of type `α`.
Here `Unit` is a type that has a single value, the unit, denoted `()`.
The unit `()` is the Lean equivalent of `None` in Python
(and `Unit` is the equivalent of `NoneType`, which is `type(None)`).

Therefore, `hello` which is defined by 

```lean
def hello := IO.println "Hello world! 👋"

#check hello
-- hello : IO Unit
```

is an action that when it's executed, will have a side-effect (print "Hello world! 👋") and return nothing of interest (the unit).
Now, you can ask `#eval` – who has access to Lean runtime – to execute this action:

```lean
#eval hello
-- Hello world! 👋
```

If instead of programming in the playground you want to create a program,
create a file `Hello.lean` whose contents are:

```lean
def hello := IO.println "Hello world! 👋"

def main := hello
```

A `main` constant with type `IO Unit` is the program entry point: 
the action that Lean runtime will execute when you run the program:

```bash
$ lean --run Hello.lean
Hello world! 👋
```

### 🎲 Random Functions

Let's now try to generate (pseudo-)random numbers with Lean.
There is in the standard library a function `IO.rand` which 
can produce random natural numbers in a given range. 
Its signature is:

```lean
#check IO.rand
-- IO.rand (lo hi : Nat) : BaseIO Nat
```

`BaseIO` is a context similar to `IO` but more restricted: actions in
this context are not allowed to throw exceptions. This is largely irrelevant
for us right now, since Lean will hapilly convert it to an `IO` context when it's needed.

To define that function that generates a random number between 1 and 6, you can define

```lean
def rollDie := IO.rand 1 6

#check rollDie
-- rollDie : BaseIO Nat
```

Using it several times yields something like:

```lean
#eval rollDie
-- 1
#eval rollDie
-- 4
#eval rollDie
-- 6
```

Consider a moment what you can do with a similar but pure value.
Its signature would be:

```lean
def rollDieWithoutIO : Nat :=
  sorry -- No implementation yet

#check rollDieWithoutIO
-- rollDieWithoutIO: Nat
```

Thus you **can** select a "random" number between 1 and 6, but 
you'd better select it carefully because it's the only one you'll ever get!

If you pick 3 for example

```lean
def rollDieWithoutIO : Nat := 3
```

then you will get

```lean
#eval rollDieWithoutIO
-- 3
#eval rollDieWithoutIO
-- 3
#eval rollDieWithoutIO
-- 3
```

There are actually some ways to deal with (pseudo-)random numbers without `IO`, but they require a different interface.


▶️ Let's `do` this
--------------------------------------------------------------------------------

We are now faced with two issues:

  1. Since the core of Lean is pure and it's pretty handy, how do 
    we mix pure and impure? 
  
  2. How do we chain impure functions to define more complex impure functions?

First note that the answer to the first point should be
asymmetric: it should not be possible to execute impure functions from 
pure ones, otherwise the careful tracking of impurity would be broken. 
But we still need to integrate pure functions as impure ones. This is actually quite
easy, with a `do` block and the `return` keyword.


```lean 
def rollDieWithoutIO : Nat := 3

def rollFake : IO Nat := do
  return rollDieWithoutIO

#eval rollFake
-- 3
```

The `do` block also solves most of the chaining problem. 
To chain actions, simply enumerate them in a do block:


```lean
def rollDie : IO Nat := 
  IO.rand 1 6

def rollDie' : IO Nat := do
  IO.println "🎲 Rolling the die ..."
  rollDie

#eval rollDie'
-- 🎲 Rolling the die ...
-- 1
```

Note that it's useless but OK to write:

```lean
def rollDie : IO Nat := do
  IO.rand 1 6
```

In this context, you chain a single `IO` action...

The real pickle comes if you want to chain two actions and have the 
second one depend on the result of the first.
For example, that's the situation if we want our information message 
to display the value of the rolled die instead. If we had a `Nat` value `die`, we could use the formatted string 
construct of Lean

```lean
def die : Nat := 3

#eval IO.println s!"🎲: {die}"
```

But unfortunately this is not what `rollDie` generates: it
produces values of type `IO Nat` instead, so we a bit more help from Lean.
That comes in the form of a `<-` symbol! In a `IO` context and in a `do` block, you can use `<-` to extract a value of type `IO α` into a value of type `α`.

For us, that means that we can do:

```lean
def rollDie : IO Nat := do
  IO.rand 1 6

def rollDie'' : IO Nat := do
  let die <- rollDie
  IO.println s!"🎲: {die}"
  return die

#eval rollDie''
-- 🎲: 2
-- 2
```

And before you ask, no, this is **not** a breach of the `IO` context! 
Yes you can "breach" the `IO` context to get a pure `die`, 
but since this is only allowed in an
enclosing `IO` context, you cannot turn an impure function into a pure one.



Control flow
--------------------------------------------------------------------------------

  - if (ex: die with verbose option)

  - mutable variables

  - loops (while, for, break, continue)


Live dangerously
--------------------------------------------------------------------------------



Use ! variants

🐍 Use Python from Lean
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

```lean
import Python

def main : IO Unit := do
  let message <- Python.eval! "'Hello world!'"
  IO.println message

#eval main
-- Hello world!
```

```lean
import Python

def main : IO Unit := do
  let sum : String <- Python.eval! "1 + 1"
  IO.println s!"1 + 1 = {sum}"

#eval main
-- 1 + 1 = 2
```

You can use `Python.exec!` to define Python constants and/or functions before
calling `Python.eval!`:

```lean
import Python

def pythonCode := "
def sum_integers_up_to(n):
    return n * (n + 1) // 2
"

def main : IO Unit := do
    Python.exec! pythonCode
    let sum : String <- Python.eval! "sum_integers_up_to(10)"
    IO.println s!"1 + 2 + ... + 10 = {sum}"

#eval main
-- 1 + 2 + ... + 10 = 55
```

Convert strings that represent Python objects to native Lean types when needed:

```lean
import Python

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
```

Spin a toupie server with extra Python libraries when you need them;
the `requests` library is required for the next example:

```bash
uvx --with requests --from git+https://github.com/boisgera/toupie toupie
```

Note that Lean 4 [raw string literals] 
– especially the hash mark variant – 
are very handy to define Python code without worrying 
about escaping backslashes and quotes.

[raw string literals]: https://lean-lang.org/doc/reference/latest//Basic-Types/Strings/#raw-string-literals


```lean
import Python

def pythonCode := r#"
import requests

URL = "https://api.chucknorris.io/jokes/random"

def get_joke():
  joke_info = requests.get(URL).json()
  return joke_info["value"]
"#

def randomJoke : IO String := do
  Python.exec! pythonCode
  let joke <- Python.eval! "get_joke()"
  return joke

#eval do
  let joke <- randomJoke
  IO.println joke
-- "Everybody Hates Chris" was originally called "Chuck Norris Hates Chris" but 
-- Chris Rock didn't want to make a series just about how he survive Chuck 
-- Norris round house kicking him EVERYDAY
```



[toupie]: https://github.com/boisgera/toupie