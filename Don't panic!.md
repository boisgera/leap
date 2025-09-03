Don't panic!
================================================================================

![Don't panic! This is fine.]

[Don't panic! This is fine.]: https://media.npr.org/assets/img/2023/01/14/this-is-fine_custom-b7c50c845a78f5d7716475a92016d52655ba3115.jpg?s=800&c=85&f=webp
<!-- The image has been backed up in the Wayback Machine -->

🐍 Exit
--------------------------------------------------------------------------------

In Python, the function [sys.exit] terminates a program and provides an error 
message (and status).

For example the Python program `kthxbye.py`

```python
import sys
sys.exit("👋") 
``` 

displays the emoji `👋` (on the standard error)


```bash
$ python kthxbye.py
👋
```

and sets an exit code of `1` (an error; `0` indicates success).

```bash
$ echo $?
1
```

The `sys.exit` function is mostly used in scripts and not in libraries, 
as it terminates the program. A slightly more realistic usage of it
is given in the `greeter.py` script:

```python
import sys

args = sys.argv[1:]
if args:
    name = " ".join(args)
    print(f"Hello {name}!")
else:
    sys.exit("❌ Please provide your name")
```

The script greets you with the name you give as arguments:

```bash
$ python greeter.py John Doe
Hello John Doe!
```

We can check that this call was a success:

```bash
$ echo $?
0
```

If you forget to provide your name, it provides you an error message

```bash
$ python greeter.py
❌ Please provide your name
```

and signals a failure:

```bash
$ echo $?
1
```


[sys.exit]: https://docs.python.org/3/library/sys.html#sys.exit


Panic!
--------------------------------------------------------------------------------

In Lean, `panic!` exits the program with a message:

```lean
def pred! (n : Nat) : Nat :=
  if n > 0 then
    n - 1
  else
    panic! "No predecessor for 0"
```

```lean
#eval pred! 7
-- 6
```

```lean
#eval pred! 0
-- PANIC at pred! ...: No predecessor for 0
-- backtrace:
```

Similarly, we can use `panic!` in the `IO` context; the file `KThxBye.lean`

```lean
def main : IO Unit := do
  panic! "👋"
```

behaves like its Python counterpart:

```bash
$ lean --run KThxBye.lean 
PANIC at main KThxBye:2:2: 👋
...

$ echo $?
1
```

Many functions and operators of the standard library have a variant 
that uses `panic!` to signal errors. 
For example to access the element of a list `xs` at the index `i`, 
you can use `xs[i]!`:

```lean
def xs := [1, 2, 3]

#eval xs[0]!
--1
#eval xs[1]!
-- 2
#eval xs[2]!
-- 3
```

This will panic if the index is out of bounds:

```lean
#eval xs[3]!
-- PANIC at List.get!Internal Init.GetElem:327:18: invalid index
-- ...
```

Similarly, to get the first element of a list, you can use:

```lean
#eval [1, 2, 3].head!
-- 1
```

Of course, if your list is empty, this will panic:

```lean
#eval [].head!
-- PANIC at List.head! ...: empty list
-- ...
```

### 💡 Exclamation point `!`

The use of the exclamation point `!` usually indicates here that the function 
is "dangerous" or "unsafe": it can panic if it encounters an error. 
This is only a convention, not a strict rule, but it's useful! 

### ℹ️ When should I `panic!`?

Some guidelines:

 1. In a script (a simple command line tool, designed to automate a repetitive
    sequence of actions), it's acceptable to use `panic!` for error handling.

    ```lean
    def main (args : List String) := do
      if args.length == 0 then
        panic! "Please provide your name"
      let name := args[0]!
      IO.println s!"Hello {name}!"

    #eval main []
    -- PANIC at main ...: Please provide your name
    -- backtrace:
    ```
    
    If you want to avoid the display of a panic message to the final user, 
    you can also separately print your custom error message to the standard 
    error and selecting a faulty error code yourself.

    ```lean
    def main (args : List String) : IO UInt32 := do
      if args.length == 0 then
        IO.eprintln "input error: Please provide your name"
        return 1 -- failure
      else
        let name := args[0]!
        IO.println s!"Hello {name}!"
        return 0 -- success

    #eval main []
    -- input error: Please provide your name
    ```

 2. When you are prototyping, `panic!` can provide temporarily a partial 
    implementation. For example, the code

    ```lean
    def divideByTwo (n : Nat) : Nat :=
      if n % 2 == 0 then
        n / 2
    ```

    does not compile but the following one does:

    ```lean
    def divideByTwo (n : Nat) : Nat :=
      if n % 2 == 0 then
        n / 2
      else
        panic! "🚧 odd numbers not handled (yet)"

    #eval divideByTwo 8
    -- 4

    #eval divideByTwo 9 
    -- PANIC at ...: 🚧 odd numbers not handled (yet)
    -- backtrace:
    ```

    Note that Lean has a keyword that means exactly "I am not
    done yet here" or "TODO": this is `sorry`:

    ```lean
    def divideByTwo (n : Nat) : Nat :=
      if n % 2 == 0 then
        n / 2
      else
        sorry
    ```

    What's nice with `sorry` is that it has a nice support at the IDE level,
    which tracks the functions that are not ready yet. However, you can't
    evaluate these partially implemented functions as easily:

    ```lean
    #eval divideByTwo 8
    -- aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
    --
    -- To attempt to evaluate anyway despite the risks, use the '#eval!' command.


    #eval divideByTwo 9 
    -- aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
    --
    -- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
    ```

3.  You can use `panic!` (directly or indirectly) as long as the error 
    never happens.

    ```lean
    def pred! (n : Nat) : Nat :=
      if n > 0 then
        n - 1
      else
        panic! "No pred for 0"

    def f (n : Nat) : Nat :=
      pred! (n * n + 1) -- This is always fine since n * n + 1 >= 1.
    ```

    Here, it's actually even better to replace your comment with an `assert!` that
    states the property that you expect to be true:

    ```lean  
    def f (n : Nat) : Nat :=
        assert! n * n + 1 >= 1
        pred! (n * n + 1)
    ```

    Because if you happen to be wrong and the property is not satisfied, 
    during the execution, Lean will check and tell you:

    ```lean
    def greet : IO Unit :=
      assert! (0 == 1)
      IO.println "Hello world!"

    #eval greet
    -- PANIC at greet ...: assertion violation: (0 == 1)
    ```

    In the case of code branches that cannot possibly be executed (but that the
    compiler requires you to define anyway), you can use `unreachable!`.

    ```lean
    def f (n : Nat) : Nat :=
      let m := n * n + 1 
      if m >= 1 then
        pred! m
      else
        unreachable!
    ```

    If you happen to be wrong about this analysis and the impossible happens,
    you will get notified with the appropriate panic:

    ```lean
    def greet : IO Unit :=
      unreachable!

    #eval greet
    -- PANIC at greet ...: unreachable code has been reached
    ```


While all this is handy, the `panic!` function should be used with care:

  - Since one cannot recover from a panic the user of a code that 
    may panic has no way to deal with its errors.

  - Panics rely on convention (the "!" in the name) but are invisible
    to the type checker. To get help from the type checker in your 
    error management, consider using `Option` or `Except` 
    – introduced in the next sections – instead of `panic!`.
   
  - If you know that the code path that leads to a `panic!` cannot happen,
    you may be able to prove it (with Lean) and avoid completely the use 
    of unsafe code. A simple example: in the following code, Lean is able
    to deduce that `0`, `1` and `2` are valid indices for the constant 
    list `[1, 2, 3]`, therefore the safe access `xs[]` can be used instead
    of the unsafe variant `xs[]!`.

    ```lean
    def xs := [1, 2, 3]

    #eval xs[0]
    -- 1
    #eval xs[1]
    -- 2
    #eval xs[2]
    -- 3
    ```

    On the other hand

    ```lean
    #eval xs[3]
    ```

    does not type check since Lean fails to prove
    `3 < xs.length` and you get an error instead.

### ⚠️ When even `panic!` fails ...

Lean does not suspend the type checker when evaluating `panic!`. 
The documentation of [Lean.Parser.Term.panic] states that at 
compile-time:

> `panic! msg` formally evaluates to `@Inhabited.default α` if the expected 
> type `α` implements `Inhabited`. 
 
and later at runtime:

> At runtime, `msg` and the file position are printed to stderr [...] 
> the process is then aborted.

[Lean.Parser.Term.panic]: https://leanprover-community.github.io/mathlib4_docs/Lean/Parser/Term.html#Lean.Parser.Term.panic

So our `pred` function is typechecked as if it returned a default value of the

```lean
#eval (default : Nat)
-- 0
```

So the `pred` function is effectively typechecked as:

```lean
def pred (n : Int) : Int :=
  if n > 0 then
    n - 1
  else
    0
```

So effectively, you cannot used `panic!` instead of a type which has not declared
a default value. Hopefully, Lean declares default values for most types;
but it cannot do anything for `Empty` for example


```lean
inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'

def fail! : Nat' :=
  panic! "Nope" -- ❌ failed to synthesize Inhabited Nat'
```

You can fix this by declaring an `Inhabited` instance for `Nat'`:

```lean
inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'

instance : Inhabited Nat' where
  default := Nat'.zero

def fail! : Nat' :=
  panic! "Nope" -- ✅ analyzed as `Nat'.zero` by the type checker
```

In many cases, you can also let Lean select a sensible default value for you
by adjoining the `deriving Inhabited` clause to the type definition:
```lean
inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'
deriving Inhabited

def default : Nat' := Inhabited.default

#eval default
-- Nat'.zero

def fail! : Nat' :=
  panic! "Nope" -- ✅ analyzed as `Nat'.zero` by the type checker
```



Option
--------------------------------------------------------------------------------

### Sentinel values

[Sentinel values] enable a primitive kind of error handling. 
The idea is to reserve some specific value(s) among the possible
returned values of a function and return them when an error 
(or "exceptional condition") occurs.

<!--
**In the C programming language.** To read the content of files on
Linux, there is a `read` function that returns a signed integer.

```C
n = read(file, buffer, count) 
```

If `n` is non-negative, that's the number of bytes that you have effectively read in your buffer. But it's `-1`, that means that an error occurred.
In this case, `-1` was the sentinel value.

The `read` function in Python doesn't work this way: 
it returns the buffer directly and raises an exception if an error occurred.
-->

For example in Python, if you want to locate substrings using `str.find`, 
this is how it goes:

```pycon
>>> "abcdefg".find("abc")
0
>>> "abcdefg".find("efg")
4
>>> "abcdefg".find("zzz")
-1
```

Here a non-negative value should be interpreted as an index (where the 
substring privided as an argument starts in `"abcdefg"`), while `-1`
means that the substring was not found: `-1` is the sentinel value.

The way the `find` method works is pretty rare in Python. Usually when a 
sentinel value is used, that's `None`. For example, to scan a dictionary
for values and avoid raising an exception when your key is not present,
you can do:

```pycon
>>> {"a": 1, "b": 2}.get("a")
1
>>> {"a": 1, "b": 2}.get("b")
2
>>> {"a": 1, "b": 2}.get("c")
>>> {"a": 1, "b": 2}.get("c") is None
True
```

but it's a bit tricky since if you are not sure that `None` is not used as
a value, you may have a false error detection:

```pycon
>>> {"a": 1, "b": 2, "z": None}.get("z")
>>> {"a": 1, "b": 2, "z": None}.get("z") is None
True
```

The situation is better in the following "PIN validity checker" example:


```pycon
>>> import re # regular expressions
>>> PIN = re.compile(r"[0-9]{4}$") # 4 digit pattern
>>> PIN.match("0000")
<re.Match object; span=(0, 4), match='0000'>
>>> PIN.match("1234")
<re.Match object; span=(0, 4), match='1234'>
>>> PIN.match("12")
>>> PIN.match("123456")
>>> PIN.match("ABCD")
```

Just to be sure what's happening here:

```pycon
>>> match = PIN.match("0000") 
>>> match is None
False
>>> type(match)
<class 're.Match'>
>>> no_match = PIN.match("ABCD") 
>>> no_match is None
True
>>> type(no_match)
<class 'NoneType'>
```

When the string is not a valid PIN, the `match` method returns `None` 
instead of a match object. 

It's often possible to catch more potential errors before the code is 
executed in Python with type annotations and static type checkers such as 
[mypy]. 

[mypy]: https://github.com/python/mypy

For example, if you declare explictly that the dictionary `d` is meant to
store string keys and integers values, 

```python
d : dict[str, int] = {"a": 1, "b": 2, "c": 3}
```

when invoked, mypy will object to a code snippet
such as 

```python
d["z"] = None
```

with

```
... error: Incompatible types in assignment (expression has type "None", target has type "int")  [assignment]
```

Now if you do

```python
import random
import string

d: dict[str, int] = {"a": 1, "b": 2, "c": 3}

random_key = random.choice(string.ascii_letters)

d.get(random_key)
```

Your Python environment may also be smart enough to infer that
in this context, the signature of the `get` method is:

```python
def get(key: str, default: None = None) -> (int | None)
```


[Sentinel values]: https://en.wikipedia.org/wiki/Sentinel_value



### Option

The standard Lean library provides an [Option] type:

[Option]: https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Option

```lean
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```

An option either "wraps" a value `a` of type `α` into `some a` or is `none`
if their is no value. 
Here is how you could use `Option` to implement a variant of the predecessor
function:

```lean
def pred? (n : Nat) : Option Nat :=
  if n > 0 then
    some (n - 1)
  else
    none
```

To deal with optional values, you match their result:

```lean
def showPred (n : Nat) : IO Unit :=
  match pred? n with
  | some m => IO.println s!"pred {n} = {m}"
  | none => IO.println s!"error: {n} has no predecessor"

#eval showPred 7
-- pred 7 = 6

#eval showPred 0
-- error: 0 has no predecessor
```

Many functions in the standard library return options; their name ends with a
question mark `?`. 


### `Option` and `do` blocks

Functions that output options can be combined in a straightforward manner. 
For example to extract two integers separated with a space in a string:

```lean
def getCoords (string : String) : Option (Nat × Nat) :=
  let parts := string.splitOn " "
  let xy_str := match parts[0]? with
  | none => none
  | some x => match parts[1]? with
    | none => none
    | some y => some (x, y)
  match xy_str with
  | none => none
  | some (x, y) => match x.toNat? with
    | none => none
    | some x' => match y.toNat? with
      | none => none
      | some y' => some (x', y')

#eval getCoords "3 4"
-- some (3, 4)

#eval getCoords "three four"
-- none
```

This is conceptually OK but it gets hard to read. However there is a common
pattern in this code: as soon as some option-valued function call fails,
we want our `getCoords` function to also fail (output `none`) and otherwise,
we extract the value and keep on computing.

This pattern is directly supported by options described in `do` blocks;
the following code is equivalent:

```lean
def getCoords' (string : String) : Option (Nat × Nat) := do
  let parts := string.splitOn " "
  let x_str <- parts[0]?
  let y_str <- parts[1]?
  let x <- x_str.toNat?
  let y <- y_str.toNat?
  return (x, y)

#eval getCoords' "3 4"
-- some (3, 4)

#eval getCoords' "three four"
-- none
```

The trick is, as usual with `do` blocks, that `Option` is a monad. 
As such, it:

  - lifts an element `a : α` to `some a : Option α`,

  - chains operations by returning the first `Option.none` which
    occurs, or `some` of the final result if all operations succeed.

```lean
def pure (a : α) : Option α := 
  Option.some a

def bind (option : Option α) (f : α -> Option β) : Option β :=
  match option with
  | none   => none
  | some a => f a
```

### ⛏️ Extracting the value

You can always pattern match an option to extract the value it contains,
but you have to deal with the case where there is no value, even if you
know that it's impossible. Two methods can help you in this case:

  - `Option.get!` which extracts the value from an option and panics 
    if the option is none.

  - `Option.get` which asks for an option **and a proof that this option
    contains a value** and extracts the value.

The first method brings us back to the strategy of errors as panics; 
the second method may require more effort but it offers more safety.
An example of the first strategy:

```lean
def list := [0, 1, 2, 4]

#check Option.get!
-- Option.get!.{u} {α : Type u} [Inhabited α] : Option α → α

#eval list[3]?.get!
-- 4

#eval list[4]?.get!
-- PANIC at Option.get! ...: value is none
```

and below the corresponding proof-based extraction. 

```lean
#check Option.get
-- Option.get.{u} {α : Type u} (o : Option α) : o.isSome = true → α

#check Option.isSome
-- Option.isSome.{u_1} {α : Type u_1} : Option α → Bool

#print Option.isSome
-- def Option.isSome.{u_1} : {α : Type u_1} → Option α → Bool :=
-- fun {α} x =>
--   match x with
--   | some val => true
--   | none => false

theorem this_is_fine : (list[3]?).isSome = true := by
  trivial

#eval list[3]?.get this_is_fine
-- 4
```

Note that here the proof we were in need for was very easy to derive.

### 🛡️ Guard

Using an option option, we can implement an age-controlled answer to the 
"Ultimate Question of Life, the Universe, and Everything":

[HHGG]: https://en.wikipedia.org/wiki/The_Hitchhiker%27s_Guide_to_the_Galaxy

```lean
def HHGG.answer (age : Nat) : Option Nat := do
  if age < 18 then
    none
  else
    return 42

#eval HHGG.answer 16
-- none

#eval HHGG.answer 50
-- some 42
```

But again, if we have several checks to do, we can expect our code to display
too much indentation for our taste. Instead, we can use `guard` in a `do`
block for `Option`. It checks a boolean condition, fails (output `none`) 
if it not satisfied and does nothing otherwise:

```lean
def HHGG.answer (age : Nat) : Option Nat := do
    guard (age >= 18)
    return 42

#eval HHGG.answer 16
-- none

#eval HHGG.answer 50
-- some 42
```

Very readable and handy!


### 🛟 Fallback

Whenever you want to try something and return it but if it fails you have a 
fallback (that may also fail!) that you want to return instead and so on
and so forth, until you're out of options and you fail, 
you can of course match the results manually and deal with them:

```lean
def readFalse (s : String) : Option Bool := do
  if s == "false" || s == "0" || s == "⊥" then
    return false
  else
    none

def readTrue (s : String) : Option Bool := do
  if s == "true" || s == "1" || s == "⊤" then
    return true
  else
    none

def readBool (s : String) : Option Bool := do
  match readFalse s with
  | some b => some b
  | none   =>
    match readTrue s with
    | some b => some b
    | none => none

#eval readBool "true"
-- some true

#eval readBool "0"
-- some false

#eval readBool "maybe?"
-- none
```

But there is a better option (pun intended 😉): `Option` is an instance of 
the [orElse] type class, which means that you can use the operator `<|>` 
like to avoid most of the boilerplate code:

```lean
def readBool (s : String) := readFalse s <|> readTrue s
```

<!--
However, if you need/want to keep a bit more control on the failure handling,
but still don't like the pattern-matching flavor of the original `readBool`
code, you can use the `try/catch` construct instead.
-->

<!--
```lean
def readBool (s : String) : Option Bool :=
  try
    readFalse s
  catch _ =>
    try
      readTrue s
    catch _ =>
      throw ()
```

(courtesy of `Option` instantiating [MonadExcept]). The underscore in this code
is supposed to capture the extra information that comes with a failure, but
with options, there is no such value (here `_` matches unit). For the same
reason, we were able to replace `failure` with `throw ()`.

To really make use fully of the try/catch pattern, we will introduce the `Except` type.
-->

[Alternative]: https://leanprover-community.github.io/mathlib4_docs/Init/Control/Basic.html#Alternative
[orElse]: https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#OrElse
[MonadExcept]: https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#MonadExcept

Except
--------------------------------------------------------------------------------

### 💬 Errors with messages

The `Except` type is very similar to `Option`. It simply adds in the error
case the ability to add some data to describe the context of the error.
I say "some data" because you get to decide the nature of this payload.

```lean
#print Except
-- inductive Except.{u, v} : Type u → Type v → Type (max u v)
-- number of parameters: 2
-- constructors:
-- Except.error : {ε : Type u} → {α : Type v} → ε → Except ε α
-- Except.ok : {ε : Type u} → {α : Type v} → α → Except ε α
```

For example, to box a boolean value into an `Except` type with string
error payload, use the type `Except String Bool`

```lean
def Result := Except String Bool

def openThePodBayDoors (magicWord := "") : Result := do
  if magicWord = "please" then
    return true
  else
    throw "What's the magic word?"

#eval openThePodBayDoors
-- Except.error "I'm sorry Dave, I'm afraid I can't do that"

#eval openThePodBayDoors "please"
-- Except.ok true
```

As usual, you can pattern match `Except` elements

```lean
def openThePodBayDoorsRetry : Result := 
  match openThePodBayDoors with
  | .ok b => Except.ok b
  | .error "What's the magic word" => openThePodBayDoors "please"
  | .error _ => Except.error "I don't know what tell you..."
```

but in `do` blocks you can also use the `try/catch` syntax:

```lean
def openThePodBayDoorsRetry : Result :=  do
  try 
    return <- openThePodBayDoors
  catch e =>
    if e == "What's the magic word" then
      return <- openThePodBayDoors "please"
    else
      throw "I don't know what to say to you..."
```

Note that if you don't need the error payload, you can convert an `Except`
element to the corresponding `Option` element with the [toOption] method.

[toOption]: https://leanprover-community.github.io/mathlib4_docs/Init/Control/Except.html#Except.toOption


### 🧬 Custom error payloads

Note error are not limited to string payloads. Adapt the error type to the
problem at hand! For example, if you try to decode DNA sequences, it makes
sense to define:

```lean
inductive NucleotideBase where
| adenine : NucleotideBase
| cytosine : NucleotideBase
| guanine: NucleotideBase
| thymine: NucleotideBase
deriving Repr

structure DecodeError where
  decoded : List NucleotideBase
  pos : Nat
  char : Char
deriving Repr

def Result := Except DecodeError (List NucleotideBase) deriving Repr
```

and then your decoding function can be:

```lean
def decodeDNA (dna : String) : Result := do
  let mut bases : List NucleotideBase := []
  for (c, i) in dna.toList.zipIdx do
    match c with
    | 'A' => bases := bases ++ [.adenine]
    | 'C' => bases := bases ++ [.cytosine]
    | 'G' => bases := bases ++ [.guanine]
    | 'T' => bases := bases ++ [.thymine]
    | _   => throw { decoded := bases, pos := i, char := c }
  return bases

#eval decodeDNA "GATTACA"
-- Except.ok [
--   NucleotideBase.guanine,
--   NucleotideBase.adenine,
--   NucleotideBase.thymine,
--   NucleotideBase.thymine,
--   NucleotideBase.adenine,
--   NucleotideBase.cytosine,
--   NucleotideBase.adenine
-- ]

#eval decodeDNA "TARATATA"
-- Except.error {
--   decoded := [NucleotideBase.thymine, NucleotideBase.adenine],
--   pos := 2,
--   char := 'R'
-- }
```

If you feel that you should instead swallow invalid characters in the decoding,
no problem, you can handle the errors throws be `decodeError` and thanks to
its payload, handle them appropriately:

```lean
def decodeDNA' (dna : String) : Result := do
  let mut bases : List NucleotideBase := []
  let mut dna := dna
  while dna != "" do
    try
      bases := bases ++ (<- decodeDNA dna)
      dna := ""
    catch decodeError =>
      bases := bases ++ decodeError.decoded
      dna := dna.drop (decodeError.pos + 1)
  return bases

#eval decodeDNA' "GATTACA"
-- Except.ok [
--   NucleotideBase.guanine,
--   NucleotideBase.adenine,
--   NucleotideBase.thymine,
--   NucleotideBase.thymine,
--   NucleotideBase.adenine,
--   NucleotideBase.cytosine,
--   NucleotideBase.adenine
-- ]

#eval decodeDNA' "TARATATA"
-- Except.ok [
--  NucleotideBase.thymine,
--  NucleotideBase.adenine,
--  NucleotideBase.adenine,
--  NucleotideBase.thymine,
--  NucleotideBase.adenine,
--  NucleotideBase.thymine,
--  NucleotideBase.adenine
--  ]
```

You may find strange that `decodeDNA'` returns a `Result` and not a 
`List NucleotideBase` because since all errors are handled in the catch
clause, this function cannot possibly throw an error. OK, we know that
but Lean doesn't! So we need to prove it. My strategy (not implemented
completely) can be found [in the annex](#annex).



 IO
--------------------------------------------------------------------------------

```lean
#check IO.rand
-- IO.rand (lo hi : Nat) : BaseIO Nat

#eval IO.rand 1 6
-- 4

#eval IO.rand 1 6
-- 2
```

`BaseIO` is the simplest IO monad of Lean. Actions of this type can have
side-effects in the real world but cannot fail.

```lean
#check BaseIO
-- BaseIO : Type → Type

#print BaseIO
-- def BaseIO : Type → Type := EIO Empty


#check EIO
-- EIO (ε : Type) : Type → Type

#print EIO
-- def EIO : Type → Type → Type := fun ε => EStateM ε IO.RealWorld


#print IO.RealWorld
-- def IO.RealWorld : Type := Unit
```

EStateM is a combined state and exception monad.

```lean
#check EStateM
-- EStateM.{u} (ε σ α : Type u) : Type u

-- The state is of type σ and each action produces a. Every state transition
-- produces a new state and:
--   - either an ok result that boxes a value of type α
--   - or an error result that boxes an error info of type ε
#print EStateM.Result
-- inductive EStateM.Result.{u} : Type u → Type u → Type u → Type u
-- number of parameters: 3
-- constructors:
-- EStateM.Result.ok : {ε σ α : Type u} → α → σ → EStateM.Result ε σ α
-- EStateM.Result.error : {ε σ α : Type u} → ε → σ → EStateM.Result ε σ α
```

For `BaseIO` actions,
  - The state σ is IO.RealWorld defined as Unit. So there is no
    associated state *managed by Lean* (the state is entirely external:
    the info that you have changed on your hard drive, in the cloud, etc.)
  - The error type is `Empty` which has no element: the action cannot fail.

```lean
#eval IO.println "Hello world!"
-- Hello world!

#check IO.println
-- {α : Type u_1} → [ToString α] → α → IO Unit
```

The `IO` monad is probably more common. Actions of this type can have
-- side-effects in the real world and can fail.

```lean
#check IO
-- IO : Type -> Type

#print IO
-- def IO : Type → Type := EIO IO.Error
```

There is a (long) list of possible errors, described by the `IO.Error` type.

```lean
#check IO.Error
-- IO.Error : Type

#print IO.Error
-- inductive IO.Error : Type
-- number of parameters: 0
-- constructors:
-- IO.Error.alreadyExists : Option String → UInt32 → String → IO.Error
-- IO.Error.otherError : UInt32 → String → IO.Error
-- IO.Error.resourceBusy : UInt32 → String → IO.Error
-- IO.Error.resourceVanished : UInt32 → String → IO.Error
-- IO.Error.unsupportedOperation : UInt32 → String → IO.Error
-- IO.Error.hardwareFault : UInt32 → String → IO.Error
-- IO.Error.unsatisfiedConstraints : UInt32 → String → IO.Error
-- IO.Error.illegalOperation : UInt32 → String → IO.Error
-- IO.Error.protocolError : UInt32 → String → IO.Error
-- IO.Error.timeExpired : UInt32 → String → IO.Error
-- IO.Error.interrupted : String → UInt32 → String → IO.Error
-- IO.Error.noFileOrDirectory : String → UInt32 → String → IO.Error
-- IO.Error.invalidArgument : Option String → UInt32 → String → IO.Error
-- IO.Error.permissionDenied : Option String → UInt32 → String → IO.Error
-- IO.Error.resourceExhausted : Option String → UInt32 → String → IO.Error
-- IO.Error.inappropriateType : Option String → UInt32 → String → IO.Error
-- IO.Error.noSuchThing : Option String → UInt32 → String → IO.Error
-- IO.Error.unexpectedEof : IO.Error
-- IO.Error.userError : String → IO.Error
```

That means thats errors in the `IO` context are manageable:

```lean
def printlnOrPanic! {α} [ToString α] (a : α) : IO Unit := do
  try
    IO.println a
  catch error => -- catch every error
    panic! s!"😱 {error}"
```

You can also adopt specific behaviors for every type of error:

```lean
def printlnOrPanicIfPermissionDenied! {α} [ToString α] (a : α) : IO Unit := do
  try
    IO.println a
  catch e =>
    match e with
    | .permissionDenied _ _ _ => panic! s!"🔒 Permision denied"
    | _ => return -- This is fine.
```

You can also collapse `catch` and `match` for brevity:

```lean
def printlnOrPanicIfPermissionDenied!' {α} [ToString α] (a : α) : IO Unit := do
  try
    IO.println a
  catch
  | .permissionDenied _ _ _ => panic! s!"🔒 Permision denied"
  | _ => return -- This is fine.
```

Actions of type `BaseIO` are automatically promoted to the `IO` type
when needed.

```lean
def printDie : IO Unit := do
  let die <- IO.rand 1 6
  IO.println s!"🎲 {die}"

#eval printDie
-- 🎲 5
```

Annex
--------------------------------------------------------------------------------

### 🧠 Safe DNA decoding


 1. First we prove a general result: 
    a `try/catch` construct where the `catch` clause  doesn't throw 
    doesn't throw. I know how to state and prove that:

    ```lean
    theorem safe_try_except {ε α} (body : Except ε α) (handler : ε -> Except ε α) :
      (∀ (e : ε), (handler e).isOk = true) -> (tryCatch body handler).isOk = true
      := by
      intro h_ok
      rw [tryCatch]
      rw [instMonadExceptOfMonadExceptOf]
      simp [tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch]
      cases body with
      | ok a =>
        rw [Except.isOk, Except.toBool]
      | error e =>
        simp
        rw [h_ok e]

 2. Then using this theorem, we prove that `decodeDNA'` doesn't throw:

    ```lean
    theorem decodeDNA'CantFail : ∀ (dna : String), (decodeDNA' dna).isOk = true := by
      admit -- 🚧 **TODO**. 😟 while loops are hard
    ```

 3. Then we implement a `get` method for `Except`, similar to the one `Option` has:

    ```lean
    def Except.get {ε α} (except : Except ε α) : except.isOk = true -> α :=
      fun ex_ok =>
        match except with
        | ok a => a
        | error _ => nomatch ex_ok
    ```

 4. We use steps 2. and 3. to define a safe `decodeDNA'` variant:

    ```lean
    def decodeDNA'' (dna : String) : List NucleotideBase := 
      Except.get (decodeDNA' dna) (decodeDNA'CantFail dna)
    ```