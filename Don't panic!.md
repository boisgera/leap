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

  - In a script, it's often acceptable to use `panic!` for error handling.

  - When you are prototyping, `panic!` can provide temporarily a partial 
    implementation. For example, the code

    ```lean
    def divideByTwo (n : Nat) : Nat :=
      if n % 2 == 0 then
        n / 2
    ```

    does not compile but

    ```lean
    def divideByTwo (n : Nat) : Nat :=
      if n % 2 == 0 then
        n / 2
      else
        panic! "🚧 odd numbers not handled"
    ```

  - You can use `panic!` (directly or indirectly) as long as the error 
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

While this is handy, the `panic!` function should be used with care:

  - Since one cannot recover from a panic the user of a code that 
    may panic has no way to deal with it.

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

Sentinel value: ex `-1`

`None` in Python

**TODO**

`.get` instead of `[]` in dicts (warning: if the dict has None in values), 
regexp match.


`match` in Python

[sentinel value]: https://en.wikipedia.org/wiki/Sentinel_value

Optional types in Python TYPING. from typing import Optional but not
a real optional, right? Just a sentinel.

### Optional values

Optional values are an alternative to `panic!` to deal with errors.
The standard Lean library provides an [Option] type:

[Option]: https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Option

```lean
inductive Option (α : Type u) where
  /-- No value. -/
  | none : Option α
  /-- Some value of type `α`. -/
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

To deal with such functions, you match their result to deal with the two 
cases (value or no value)

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


### `Option` as a monad 

Functios that output options can be combined in a straightforward manner. 
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
pattern in this code: as soon as some option-returning function call fails,
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

  - lifts an element `a : `α` to `some a : Option α`,

  - chains operations by returning the first `Option.none` which
    occurs, or `some` of the final result if all operations succeed.

```lean
def pure : α → Option α := Option.some

def bind : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a
```

### 🍬 More Sugar

**TODO:** `failure` and `orElse` and `try/catch`


You can use `failure` instead of `none` if that conveys better the intent of
your code:

```lean
def pred? (n : Nat) : Option Nat :=
  if n > 0 then
    some (n - 1)
  else
    failure
```

(that works because all Monad types are automatically [Alternative].)

Whenever you want to try something and return it but if it fails you have a 
fallback (that may also fail!) that you want to return instead and so on
and so forth, until you're out of options and you fail, 
you can of course match the results manually and deal with them:

```lean
def readFalse (s : String) : Option Bool :=
  if s == "false" || s == "0" || s == "⊥" then
    return false
  else
    none

def readTrue (s : String) : Option Bool :=
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
    | none => failure

#eval readBool "true"
-- some true

#eval readBool "0"
-- some false

#eval readBool "maybe?"
-- none
```

But there is a better option (pun intended 😉): `Option` instantiates 
the [orElse] type class, which means that you can use the operator `<|>` 
like to avoid most of the boilerplate code:

```lean
def readBool (s : String) := readFalse s <|> readTrue s
```

However, if you need/want to keep a bit more control on the failure handling,
but still don't like the pattern-matching flavor of the original `readBool`
code, you can use the `try/catch` construct instead.

```lean
def readBool (s : String) : Option Bool :=
  try
    readFalse s
  catch _ =>
    try
      readTrue s
    catch _ =>
      failure
```

(courtesy of `Option` instantiating [MonadExcept])

[Alternative]: https://leanprover-community.github.io/mathlib4_docs/Init/Control/Basic.html#Alternative
[orElse]: https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#OrElse
[MonadExcept]: https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#MonadExcept

Except
--------------------------------------------------------------------------------

Python: sys.exit is an exception :


### Details

Actually, `sys.exit()` raises a `SystemExit` exception, which is a subclass of `BaseException`, not `Exception`. This is why the above code does not catch it.
But you can still catch it with:

```python
try:
    sys.exit("👋")
except SystemExit as e:
    print("🛑")
```
 or with a bare except:

```python
try:
    sys.exit("👋")
except:
    print("🛑")
```

Both these code snippers will succeed and print 🛑.

🚧 **TODO**
   
   - Except as an enhanced `Option` with error information
     (message or something else)

   - `Except.toOption`

   - JSON example

   - try catch syntax (instantiate `MonadExcept`)

---
failure, throw, andThen, try catch


```lean
def f (i : Nat) : Option Nat := do
  let value <- list[i]?
  return value

#eval f 0

#eval f 3

def g (i : Nat) : Option Nat := do
  match list[i]? with 
  | none => none
  | some value => some value

#eval g 0

#eval g 3

def h (i : Nat) : Option Nat := do
  match list[i]? with 
  | none => failure
  | some value => return value


#eval h 0

#eval h 3

def k (i : Nat) : Option Nat := do
  match list[i]? with 
  | none => throw ()
  | some value => return value

-- Different behavior now

#eval k 0
#eval k 3

def get (i : Nat) : Option Nat := do
  match list[i]? with 
  | none => return 0
  | some value => return value

#eval k 0
#eval k 3

def getOrZero? (i : Nat) : Option Nat := do
  get i <|> return 0

-- But how do we "unpack" the some (this is a some for certain!). 
-- We have "lost" the information that it's a success "in the implementation"
-- unless we match the result (which we can do)

def getOrZero?' (i : Nat) : Option Nat := do
  let mut result := 0
  try
    result <- get i
  catch _ => 
    result := 0
  return result


def getOrZero?'' (i : Nat) : Option Nat :=
  try
    return (<- get i)
  catch _ => 
    return 0

-- Try cannot solve the "ensure there is no error" issue? Try doesn't get us
-- out of the monad ... We need some good old pattern matching for that.
-- Even worse, the info that we have handled all possible errors is lost...

-- So try catch is good also long as you want to have alternatives, handle
-- errors somehow but keeping the possibility of errors here.
-- That make sense since in some monads we CANNOT unbox the result...

-- def getOrZero?''' (i : Nat) : Nat :=
--   try
--     get i
--   catch _ => 
--     0
```



---

 IO
 ----------------------------

   - instantiate MonadExcept (try catch syntax)

   - list / use "POSIX"-like error set

   - custom error types with IO (EIO and replace `IO.Error` with custom error type)


# Misc/ / Sandbox / Appendix


**TODO** Except as Option with extra info. Example: ADN Parsing, location of
the error.

    For example

    ```lean
    def f (n : Nat) : Nat :=
      let list := List.range (n + 1)
      list[n / 2] -- ❌ failed to prove index is valid [...]
    ```

    but some experimentation with the panicking version of `f`
    convinces us that the index is always valid:

    ```lean
    def f' (n : Nat) : Nat :=
      let list := List.range (n + 1)
      list[n / 2]!

    #eval f' 0
    -- 0
    #eval f' 1
    -- 0
    #eval f' 2
    -- 1
    #eval f' 3
    -- 1
    #eval f' 4
    -- 2
    ```

    If we are in a hurry, we can instead state the result we need to ensure
    that the index is valid, admit the proof and use the "dangerous" version
    `#eval!` of `#eval` instead:

    ```lean
    def f (n : Nat) : Nat :=
      let list := List.range (n + 1)
      have h : n / 2 < list.length := by admit
      list[n / 2]

    #eval! f 0
    -- 0
    #eval! f 1
    -- 0
    #eval! f 2
    -- 1
    #eval! f 3
    -- 1
    #eval! f 4
    -- 2
    ```

    When you have more time, you can come back and fill in the proof

    ```lean
    def f (n : Nat) : Nat :=
      let list := List.range (n + 1)
      have h : n / 2 < list.length := by
        rw [List.length_range] -- n : Nat ⊢ n / 2 < n + 1
        apply Nat.lt_succ_of_le -- n : Nat ⊢ n / 2 ≤ n
        exact Nat.div_le_self n 2 -- ✅
      list[n / 2]

    #eval f 0
    -- 0
    #eval f 1
    -- 0
    #eval f 2
    -- 1
    #eval f 3
    -- 1
    #eval f 4
    -- 2
    ```

    Note that we have used the following theorems provided by Lean:

    ```lean
    #check List.length_range
    -- ⊢ ∀ {n : Nat}, (List.range n).length = n
    #check Nat.lt_succ_of_le
    -- ⊢ ∀ {n m : Nat}, n ≤ m → n < m.succ
    #check Nat.div_le_self
    -- ⊢ ∀ (n k : Nat), n / k ≤ n
    ```

    At this final stage, you have avoided all operations that may panic.