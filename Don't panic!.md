Don't panic!
================================================================================


In Lean, we can use `panic!` to signal an error and exit the program with a message:

```lean
def pred (n : Nat) : Nat :=
  if n > 0 then
    n - 1
  else
    panic! "No pred for 0"
```

```lean
#eval pred 7
6
```

```lean
#eval pred 0
PANIC at pred ...: No pred for 0
...
```

Similarly, panic can be used for example in the `IO` context:

```lean
def kthxbye : IO Unit := do
  IO.println "OK, thanks"
  panic! "bye!"
```

Not that there is no way to recover from a panic, so it is best to use it
only for situations that are truly unrecoverable (or as a temporary measure
in prototyping).

### Do not mess with the type cheker

Lean does not suspend the type checker when evaluating `panic!`. 
Instead, it follows the following compile-time rule:

> panic! msg formally evaluates to @Inhabited.default α if the expected type α 
> implements Inhabited. 

And later:

> At runtime, msg and the file position are printed to stderr unless the C
> function lean_set_panic_messages(false) has been executed before. 
> If the C function lean_set_exit_on_panic(true) has been executed before, 
> the process is then aborted.

So our `pred` function is typechecked as if it returned a default value of the

```lean
#eval (default : Nat)
0
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


def fail : Nat' :=
  panic! "Nope"
```


```lean
instance : Inhabited Nat' where
  default := Nat'.zero

def fail' : Nat' :=
  panic! "Nope"
```

You can also let Lean automatically select a default value for you:

```lean
inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'
  deriving Inhabited
```

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

will fail and print 👋[^1].

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