
```lean4
import Batteries.Lean.Float

namespace Sandbox
```

# Loops

Loops are everywhere in imperative programs but they don't exist in pure FP.
(partially a lie but a useful one).
Recursion is used (directly or indirectly) to achieve the same goals.

What are loops used for? If you exclude loops that produce some side-effect,
for loops that iterate over a collection read some initial state,
the **accumulator**, **combine** it with a freshly read value from the
collection and repeat the action until the collection has been fully traversed.

Note: for loops over a collection *terminate*. While/repeat loops, that's unclear...


Consider the typical computation of a sum of floating-point numbers:

```python
def sum(xs : list[float]) -> float:
  s = 0.0
  for x in xs:
    s = s + x
  return s
```

```pycon
>>> sum([0.1, 0.2, 0.3])
0.6000000000000001

We can't do that in Lean because with cannot mutate the variable `sum`.
Instead let's do what's natural and use pattern matching;
that naturally lead us to recursion.

```lean4
def sum (xs : List Float) : Float :=
  match xs with
  | [] => 0.0
  | x :: xs => x + sum xs

#eval sum [0.1, 0.2, 0.3]
-- 0.600000
```

Note: Lean does not display "enough" precision by default to know for sure
what float has been produced. We'll get back to that in a moment, we let
it slide atm.

TODO: easier to delay tail-recursive concept to the left-associative version
of the sum since

Note that when we do that kind of recursion, the multiple calls to `sum`
that occurs are still "alive" on the call stack until we reach the empty
list, since we have to keep the function variable `x` to make a sum with
the partial sum to be able to remove the function from the call stack.
This will ultimately lead us to a stack overflow for large lists of floats.

```lean4
#check List.range
-- List.range (n : Nat) : List Nat

#eval List.range 3
-- [0, 1, 2]

#eval 3 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum
-- 0.600000

#eval 100 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum
-- 505.000000

#eval 100_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum
-- 500005000.000000

#eval 1_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum
-- 50000050000.000000
```

```lean
#eval 10_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum
-- Server process crashed, likely due to a stack overflow or a bug.
```

This accumulation of functions environment on the call stack has to happen
because there tasks are not finished after the recursive call. If instead
we manage to make the recursive call the last call of the function,
that is if our function is not only recursive but **tail-recursive**,
since Lean implements **tail-call optimization**, we can grow our list
only limited by the memory allocated to our process, not by the size of
the stack.

The trick to do that is to "push" the state each function is still holding,
here the float which is meant to be added to the sum,
to the next function. So we need an auxiliary function

```lean4
def sumAux (xs : List Float) (x0 : Float) : Float :=
  match xs with
  | [] => x0
  | x :: xs => sumAux xs (x + x0)

def sum' (xs : List Float) : Float :=
  sumAux xs 0.0

#eval 1_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum'
-- 50000050000.000000
```

Expensive but works!
```lean
#eval 10_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum'
-- 5000000500000.000000

Note that Python doesn't implement tail-call optimization so the translation
of this pattern to Python will still create a stack overflow.
```

Now if we think for a minute we have not exactly performed the same computation
in Python and in Lean. In Python our initial loop has computed

```python
>>> ((0.0 + 0.1) + 0.2) + 0.3
0.6000000000000001
```

which is the same as

```python
>>> 0.0 + 0.1 + 0.2 + 0.3
0.6000000000000001
```

since `+` is left-associative in Python.

The full precision can be displayed with

```python
>>> x = 0.0 + 0.1 + 0.2 + 0.3
>>> print(f"{x:.100g}")
0.600000000000000088817841970012523233890533447265625
```

Lean has the same convention: `+` is left-associative, so if we ask for the
full-precision display (we need to import `Batterries.Lean.Float` for that),
we get:

```lean4
#eval 0.0 + 0.1 + 0.2 + 0.3 |>.toStringFull |> IO.println
-- 0.600000000000000088817841970012523233890533447265625

#eval ((0.0 + 0.1) + 0.2) + 0.3 |>.toStringFull |> IO.println
-- 0.600000000000000088817841970012523233890533447265625

#eval (0.0 + 0.1 + 0.2 + 0.3) == (((0.0 + 0.1) + 0.2) + 0.3)
-- true
```

But our computation of the sum says something different:

```lean4
#eval sum [0.1, 0.2, 0.3] |>.toStringFull |> IO.println
-- 0.59999999999999997779553950749686919152736663818359375

#eval sum' [0.1, 0.2, 0.3] |>.toStringFull |> IO.println
-- 0.59999999999999997779553950749686919152736663818359375

end Sandbox
```
