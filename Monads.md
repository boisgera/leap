

Let's convert the number 255 into its hexadecimal representation.
With Lean, that can be achieved with the following code:

```lean
#eval "0x" ++ String.mk (Nat.toDigits 16 255)
-- "0xff"
```

We can generalize this operation to any number `n`:

```lean
def hex₀ (n : Nat) : String :=
  "0x" ++ String.mk (Nat.toDigits 16 n)

#eval hex₀ 0
-- "0x0"
```

The description of the implementation of `hex₀` is the following:

  - first convert the number `n` into a list of digits (character) 
    in base 16 using `Nat.toDigits 16 n`,
  - then convert this list of characters into a `String` using `String.mk`,
  - finally prepend the string "0x" to the result.

The pipe operator `|>` of Lean (also present in Elixir, OCaml, R, etc.) 
can make this code more faithful to this description:
`x |> f` is a syntaxic sugar for `f x` where `f` is a function and 
`x` its argument. It also is left associative, so we can chain 
multiple function applications together:
`x |> f |> g` means  `(x |> f) |> g`, that is `g (f x)`.

Using the pipe operator, we could define `hex₁` as follows:

```lean
def hex₁ (n : Nat) : String :=
  n |> fun n => Nat.toDigits 16 n |> String.mk |> fun s => "0x" ++ s
```

Note that the |> operator has low precedence, so that we don't need to use 
parentheses to separate its arguments.

And afterwards we can also 

  - remember how currying works and what `Nat.toDigits 16` represents,

  - learn that we can use ·[^centerdot] as a placeholder for arguments in 
    function definitions
    (see [Sugar for simple functions]in the [Lean documentation overview])

[Sugar for simple functions]: https://docs.lean-lang.org/lean4/doc/lean3changes.html#sugar-for-simple-functions
[Lean documentation overview]: https://docs.lean-lang.org/lean4/doc/

[^centerdot]: To get `·`, type either `\.` or `\centerdot` in the Lean editor.


and simplify the function into


```lean
def def hex₂ (n : Nat) : String :=
  n |> Nat.toDigits 16 |> String.mk |> ("0x" ++ ·)
```

```lean
def hex := hex₂

#eval hex 0
-- "0x0"

#eval hex 42
-- "0x2a"

#eval hex 255
-- "0xff"

#eval hex 4096
-- "0x1000"
```

----------



Towards 

```lean
def one_plus_one : IO Unit := do
  let result ← IO.Process.run { 
    cmd := "python3", 
    args := #["-c", "print(1 + 1)"] 
  }
  IO.println s!"1 + 1 = {result}"

#eval one_plus_one
-- 1 + 1 = 2
```

with bind, unboxing impossibility, etc. Compare with the pure stuff.


**TODO:**


  - POW: >>= easier than "bind"

  - POW: easier to understand >>= if |> is understood first
    example:

    (give and example of |> in the context of a data pipeline
    process?)

    #eval IO.FS.readFile "collatz.py" >>= IO.println

  - do block

  - do block with pure functions : `Id.run`

  - call counter example

  - functions with computation graphs (ie tracing)

  - PasswordProtected monad (?)

  - AccountTransaction monad (?)

  - PRNG (explicit and implicit)

  - Kleisli (fish) operator >=> 

  - Option and Except

  - State

  - IO
  