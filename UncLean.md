UncLean
================================================================================

🗑️ Embrace impurity
--------------------------------------------------------------------------------

In programming, functions can take inputs, process them, and
return ouputs. But they can also have various kind of side-effects: 
print messages in you terminal, send e-mails, search the Internet ... 
even order lunch!

![The Enunciation Apocalypse]

[The Enunciation Apocalypse]: https://scontent-cdg4-3.xx.fbcdn.net/v/t39.30808-6/532953901_24490135003936932_7732910830382145601_n.jpg?_nc_cat=110&ccb=1-7&_nc_sid=aa7b47&_nc_ohc=qjzUJrpukJYQ7kNvwFyHj2L&_nc_oc=AdluCJNAJctXdZR9pSI6o8UviHpup3a8cBaudmzpIp5UrLly8vwdyhOj37x-lpcAuAI&_nc_zt=23&_nc_ht=scontent-cdg4-3.xx&_nc_gid=_6IzYZREoGtgmSuKScPszA&oh=00_AfWoe-jWnl7kXSuU5NDTSQjnETbPMptTujsfGxe1OWvhOw&oe=68ABE55A

In this respect they differ from mathematical functions that do not interact
with the outside world and will always give the same outputs for the same
inputs: they are **pure**. They are very simple conceptually!

Functions with potential side-effects – **impure** functions -- 
are carefully tracked by the Lean type system; in the simplest cases,
they "live" in the `IO` context.

Consider the `IO.println` function which prints any Lean value
(which is representable as a `String`)

```lean
#eval IO.println "Hello world! 👋"
-- Hello world! 👋
```
Its signature (when restricted to inputs of type `String`) is:

```lean
#check IO.println (α := String)
-- IO.println : String → IO Unit
```

which means that it returns outputs of type `IO Unit`.
A value of type `IO α` is an action that can be executed to yield some side-effects and return a value of type `α`.
Here `Unit` is a type that contains a single value, the unit, denoted `()`.
This unit `()` is the Lean equivalent of `None` in Python[^1].

[^1]: and `Unit` is the equivalent of `NoneType`, which is `type(None)`.

Therefor, `hello` which is defined by 

```lean
def hello := IO.println "Hello world! 👋"

#check hello
-- hello : IO Unit
```

is an action that when it's executed, will have a side-effect (print "Hello world! 👋") and return nothing of interest (the unit).

```lean
#eval hello
-- Hello world! 👋
```

Not that `#eval` will happily execute your action and display its result.

Another example, consider the function `IO.rand` that can generate random 
natural numbers in a given range. Its signature is:

```lean
#check IO.rand
-- IO.rand (lo hi : Nat) : BaseIO Nat
```

`BaseIO` is a context similar to `IO` but more restricted: actions in
this context are not allowed to throw exceptions. This is largely irrelevant
for now, Lean will hapilly convert it to an `IO` context when it's needed.

To define that function that rolls a dice, you can define

```lean
def rollDice := IO.rand 1 6

#check rollDice
-- rollDice : BaseIO Nat
```

and to use it

```lean
#eval rollDice
-- 1
#eval rollDice
-- 4
#eval rollDice
-- 6
```

Consider a moment what you can do with a similar but pure function.
Its signature would be something like:

```lean
def rollDiceWithoutIO : Nat :=
  sorry -- No implementation yet

#check rollDiceWithoutIO
-- rollDiceWithoutIO: Nat
```

Thus you can select a "random" number between 1 and 6, but select it carefully
because it's the only one you'll ever get!

If you pick 3 for example

```lean
def rollDiceWithoutIO : Nat :=
  3
```

then you will get

```lean
#eval rollDiceWithoutIO
-- 3
#eval rollDiceWithoutIO
-- 3
#eval rollDiceWithoutIO
-- 3
```

There are ways to deal with (pseudo-)random numbers using only pure functions,
but they require a different interface.













Use an Imperative Style
--------------------------------------------------------------------------------

**TODO.**

  - Pure to impure, 
  - Composition of actions, etc.
  - Imperative style, do, let mut, <-, := etc. loops, etc (control flow)


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