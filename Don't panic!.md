Don't panic!
================================================================================

![Don't panic! This is fine.]

[Don't panic! This is fine.]: https://media.npr.org/assets/img/2023/01/14/this-is-fine_custom-b7c50c845a78f5d7716475a92016d52655ba3115.jpg?s=800&c=85&f=webp

<!-- 
Web archive backup: https://web.archive.org/web/20250703145700im_/https://media.npr.org/assets/img/2023/01/14/this-is-fine_custom-b7c50c845a78f5d7716475a92016d52655ba3115.jpg?s=800&c=85&f=webp 
-->

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

Another example from the standard library: try to access the element of a list
at an arbitrary index, you can use:

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

> [!TIP] 
> The use of the exclamation mark `!` indicates here that the function 
> is "dangerous", "unsafe" and can panic in case of an error. 
> This is a convention that is frequently used 
> in the standard library and something we should mimic. 
> So to begin with we should rename our previous functions 
> `pred` and `kthxbye` to  `pred!` and `kthxbye!` respectively:
>
> ```lean
> def pred! (n : Nat) : Nat :=
>   if n > 0 then
>     n - 1
>   else
>     panic! "No pred for 0"
> ```
>
> ```lean
> def kthxbye! : IO Unit := do
>   IO.println "OK, thanks"
>   panic! "bye!"
> ```

Not that there is no way to recover from a panic, so it is best to use it
only for situations that are truly unrecoverable (or as a temporary measure
in prototyping).

> [!WARNING] 
> 
> ### When `panic!` fails ...
>
> Lean does not suspend the type checker when evaluating `panic!`. 
> Instead, it follows the following compile-time rule:
>
> > `panic! msg` formally evaluates to `@Inhabited.default α` if the expected 
> > type `α` implements `Inhabited`. 
> 
> And later:
>
> > At runtime, `msg` and the file position are printed to stderr unless the C
> > function `lean_set_panic_messages(false)` has been executed before. 
> > If the C function `lean_set_exit_on_panic(true)` has been executed before, 
> > the process is then aborted.
>
> So our `pred` function is typechecked as if it returned a default value of the
> 
> ```lean
> #eval (default : Nat)
> -- 0
> ```
> 
> So the `pred` function is effectively typechecked as: 
> 
> ```lean
> def pred (n : Int) : Int :=
>   if n > 0 then
>    n - 1
> else
>    0
> ```
>
> So effectively, you cannot used `panic!` instead of a type which has not declared
> a default value. Hopefully, Lean declares default values for most types; 
> but it cannot do anything for `Empty` for example
> 
> ```lean
> inductive Nat' where
>   | zero : Nat'
>   | succ (n : Nat') : Nat'
> 
> 
> def fail : Nat' :=
>   panic! "Nope"
> ```
>
>
> ```lean
> instance : Inhabited Nat' where
>   default := Nat'.zero
>
> def fail' : Nat' :=
>   panic! "Nope"
> ```
> In most cases, you can also let Lean automatically select a default value for you:
>
> ```lean
> inductive Nat' where
>  | zero : Nat'
>  | succ (n : Nat') : Nat'
>  deriving Inhabited
> ```

### TODO: what's going on with `IO`?

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



----

The Python closest equivalent of `panic!` in Python is `sys.exit()`. 

```python
import sys
```

```python
sys.exit("👋")
👋
``` 

So even if you try to catch all the types of exceptions, you will not manage to catch the exit call; the code

```python
try:
    sys.exit("👋")
except Exception:
    print("🛑")
```

will fail and print 👋.

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
