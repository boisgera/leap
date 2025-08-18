Don't panic!
================================================================================

![Don't panic! This is fine.]

[Don't panic! This is fine.]: https://media.npr.org/assets/img/2023/01/14/this-is-fine_custom-b7c50c845a78f5d7716475a92016d52655ba3115.jpg?s=800&c=85&f=webp
<!-- The image has been backed up in the Wayback Machine -->

🐍 Exit
--------------------------------------------------------------------------------

In Python you can call the function [sys.exit] to terminate a program 
and provide an error message (and status).

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

and provides an exit code of `1` that signals an error 
(`0` indicates success).

```bash
$ echo $?
1
```

The `sys.exit` function is mostly used in scripts and not in libraries, 
as it terminates the program. A slightly more realistic usage is given 
in the `greeter.py` script:

```python
import sys

args = sys.argv[1:]
if args:
    name = " ".join(args)
    print(f"Hello {name}!")
else:
    sys.exit("❌ Please provide your name")
```

The script is supposed to work like that:

```bash
$ python greeter.py John Doe
Hello John Doe!

and we can check that this call was a success.

```bash
$ echo $?
0
```

But if you forget to provide your name:

```bash
$ python greeter.py
❌ Please provide your name
```

and this is indeed signalled as an error:

```bash
$ echo $?
1
```


[sys.exit]: https://docs.python.org/3/library/sys.html#sys.exit


Panic!
--------------------------------------------------------------------------------

In Lean, we can use `panic!` to exit the program with a message:

```lean
def pred (n : Nat) : Nat :=
  if n > 0 then
    n - 1
  else
    panic! "No pred for 0"
```

```lean
#eval pred 7
-- 6
```

```lean
#eval pred 0
-- PANIC at pred ...: No pred for 0
-- backtrace:
```

Similarly, panic can be used in the `IO` context:

```lean
def kthxbye : IO Unit := do
  IO.println "OK, thanks"
  panic! "bye!"
```

```lean
#eval kthxbye
-- OK, thanks
-- PANIC at kthxbye ...: bye!
-- backtrace:
```

A common example: to access the element of a list at an arbitrary index, 
you can use:

```lean
def list := [1, 2, 3]

#eval list[0]!
--1
#eval list[1]!
-- 2
#eval list[2]!
-- 3
```

Note however that this will panic if the index is out of bounds:

```lean
#eval list[3]!
-- PANIC at List.get!Internal Init.GetElem:327:18: invalid index
backtrace:
```

Similarly, to get the first element of a list, you can use:

```lean
def list : List Nat := [1, 2, 3]

#eval list.head!
-- 1
```

Of course, if your list is empty, this will panic:

```lean
def list : List Nat := []

#eval list.head!
-- PANIC at List.head! ...: empty list
backtrace:
```

**TODO.** Useful backtrace example?

### 💡 Naming convention: exclamation point `!`

The use of the exclamation point `!` indicates here that the function 
is "dangerous" or "unsafe" by which we mean that it can panic in case of an error. 
This is a convention that is frequently used in the standard library and 
something we should strive to mimic. 
So to begin with we should rename our previous functions 
`pred` and `kthxbye` to  `pred!` and `kthxbye!` respectively:

```lean
def pred! (n : Nat) : Nat :=
  if n > 0 then
    n - 1
  else
    panic! "No pred for 0"
``` 

```lean
def kthxbye! : IO Unit := do
  IO.println "OK, thanks"
  panic! "bye!"
```

### ℹ️ When should I `panic!`?

Some guidelines (YMMV):

  - When you prototype a function and you realise that there is a corner case
    that you don't want to deal with right now, you can use `panic!` to
    quickly satisfy the type checker.

    ```lean
    def inv (x : Float) := Float
      if x != 0 then
        panic! "Please don't invert 0"
      else
        1.0 / x
    ```

    The handy thing is that you don't have the change the function signature
    (here `Float -> Float`) to continue making some progress.

  - Something you in a given context, you know that the `panic!` is unreachable
    and you don't want to explain to Lean why it is unreachable (at least
    not right now). For example:

    ```lean
    def pred! (n : Nat) : Nat :=
      if n > 0 then
        n - 1
      else
        panic! "No pred for 0"

    def f (n : Nat) : Nat :=
      pred! (n * n + 1)
    ```

While this is handy, the "panic!" function should be used with care:

  - It doesn't inform the type checker that some function may fail,
    which is a pity since if you do, you can use it to help you check
    that your code handles them properly. To go that route, consider
    the `Option` or `Except` types instead, introduces later in this 
    document. A simple example would be to replace `pred!` with:

    ```lean
    def pred? (n : Nat) : Option Nat :=
      if n > 0 then
        some (n - 1)
      else
        none

    #eval pred 7
    -- some 6

    #eval pred 0
    -- none
    ```

  - If you know for sure that an error cannot happen, tell it that to the type 
    system! Of course, the type system will only accept your argument if you
    provide a proof. But if you are in a hurry, you can still admit the proof
    temporarily and come back later to fill in the blanks.

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

#### TODO: what's going on with `IO`?

**Fails** with:
```lean
🔴 #eval (default : IO Unit)
(`Inhabited.default` for `IO.Error`)
```

**Succeeds** with:
```lean
🟢 #eval (default : IO.Error)
(`Inhabited.default` for `IO.Error`)
```


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


Option
--------------------------------------------------------------------------------

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

#eval getCoords "douze quarante-deux"
-- none
```

Imperative style with the `do` block:

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

#eval getCoords' "douze quarante-deux"
-- none
```

As a monad, `Option`:

  - lifts an element `a : `α` to `some a : Option α`,

  - chains operations by returning the first `Option.none` which
    occurs, or `some` of the final result if all operations succeed.

```lean
def pure : α → Option α := Option.some

def bind : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a
```




Except
--------------------------------------------------------------------------------

🚧 **TODO**
   
   - Except as an enhanced `Option` with error information
     (message or something else)

   - `Except.toOption`

   - JSON example

   - try catch syntax (instantiate `MonadExcept`)

 IO
 ----------------------------

   - instantiate MonadExcept (try catch syntax)

   - list / use "POSIX"-like error set

   - custom error types with IO (EIO and replace `IO.Error` with custom error type)
