
```lean4
import Lean
```

Interactive Commands
================================================================================

Source: [Interacting with Lean](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/)


`#eval`
--------------------------------------------------------------------------------

The `#eval` command can do a lot of simple things.

### Displaying expressions

```lean4
#eval 0
-- 0

#eval 1 + 1
-- 2
```

### Resolving constants


```lean4
def name := "L∃∀N"

#eval name
-- "L∃∀N"
```

### Executing `IO` actions

```lean4
#eval IO.println "Hello world!"
-- Hello world!
```

### Evaluating propositions

```lean4
#eval 0 ≤ 1
-- true
```

### Multi-line expressions

One-liners are not required; complex expressions work too:

```lean4
#eval
  let greet := fun name? : Option String =>
    let name := match name? with
    | some name => name
    | none => "Odysseus"
    s!"Hello {name}!"
  greet name
-- "Hello L∃∀N!"
```

### Type checking first

Everything is typechecked beforehand:

```lean4
#eval 1 + "Hello"
-- failed to synthesize instance of type class
--   HAdd Nat String ?m.1

-- Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

### Printing the result

`#eval e` computes `e`, then needs some way to print the result as text.
It looks for an instance for the type of `e`, tried in this order:

- `ToExpr` converts the value back into a Lean `Expr` — the same kind of
  term the elaborator itself works with — so `#eval` can pretty-print it
  exactly as you would write it in source. This is why `#eval "hi"` below
  prints `"hi"`, quotes included: it reconstructs the string *literal*,
  not just the characters it contains.
- `Repr`, tried if there is no `ToExpr` instance, produces a readable
  textual representation directly, without going through the elaborator.
- `ToString`, tried if there is no `Repr` instance either — the same
  conversion used by `IO.println` and string interpolation (`s!"..."`).

For example:

```lean4
#eval "hi"
-- "hi"
```

If none of the three instances exists, `#eval` tries to auto-derive a
`Repr` instance for the type on the spot. For example, this `structure`
defines none of them, yet still prints:

```lean4
structure Pt where
  x : Nat
  y : Nat

#eval Pt.mk 1 2
-- { x := 1, y := 2 }
```

When even auto-derivation isn't possible — for example because the value
is a function, which has no meaningful textual form — `#eval` fails:

```lean4
def succ (n : Nat) : Nat := n + 1

#eval succ
-- could not synthesize a `Repr` or `ToString` instance for type
--   Nat → Nat
```

### Monad support

`IO` is actually a special case of a larger category supported by `#eval`.

If `e : m τ` for some monad `m`, `#eval` also needs to know how to run that
monad, independently of how it displays the result. If `e` is a monadic
value of type `m τ`, the command tries to adapt the monad `m` to one of the
monads that `#eval` supports, which include `IO`, `CoreM`, `MetaM`,
`TermElabM`, and `CommandElabM`. Users can define `MonadEval` instances to
extend the list of supported monads.

### Proposition support

The expressions `0 = 0` and `0 < 1` evaluate (via `#eval`) to booleans:

```lean4
#eval 0 = 0
-- true

#eval 0 ≤ 1
-- true
```

But they are not booleans, they are propositions. These examples work with
`#eval` because they are decidable propositions, whose truth value (a
boolean) can be systematically computed by a verified algorithm. `#eval`
does that automatically; explicitly, we could instead write:

```lean4
#eval decide (0 = 0)
-- true

#eval decide (0 < 1)
-- true
```

If Lean doesn't manage to determine that a proposition is decidable,
`#eval` fails:

```lean4
#eval ∀ x y z n : Nat, n > 2 ∧ x > 0 ∧ y > 0 ∧ z > 0 → x ^ n + y ^ n ≠ z ^ n
```

The truth value of Fermat's Last Theorem cannot be evaluated this way,
since we haven't gone through the (very complex) task of giving Lean a
verified proof of it.

`#check`
--------------------------------------------------------------------------------

The `#check e` command verifies that the expression `e` type checks
correctly and displays its type, or throws an error otherwise.

```lean4
#check 0
-- 0 : Nat

#check 0 + "Hello!"
-- failed to synthesize instance of type class
--   HAdd Nat String ?m.5

-- Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

`#check e` does not *reduce* your expression `e`:

```lean4
#check 1 + 1
-- 1 + 1 : Nat
```

It can still simplify how the expression is displayed — for example, by
dropping parentheses that turn out to be unnecessary (if you added them out
of uncertainty about operator precedence and associativity), or by
normalizing non-standard spacing and indentation:

```lean4
#check 1+1  +  1
-- 1 + 1 + 1 : Nat

#check (1 + 1) + 1
-- 1 + 1 + 1 : Nat

#check 1 + (1 + 1)
-- 1 + (1 + 1) : Nat
```

Unlike `#eval`, `#check e` doesn't need `e` itself to be printable as a
value — only its type needs to be displayed. For example, this works
perfectly, even though `succ` couldn't be `#eval`'d above:

```lean4
#check succ
-- succ (n : Nat) : Nat
```

### Additional examples

```lean4
#check 0 = 0
-- 0 = 0 : Prop

#check decide (0 = 0)
-- decide (0 = 0) : Bool

#check 0 == 0
-- 0 == 0 : Bool

#check 0 < 1
-- 0 < 1 : Prop

#check decide (0 < 1)
-- decide (0 < 1) : Bool

#check Ord.compare 0 1 == Ordering.lt
-- compare 0 1 == Ordering.lt : Bool
```

`#print`
--------------------------------------------------------------------------------

`#print ident` looks up `ident` in the environment and displays its
definition:

```lean4
#print succ
-- def succ : Nat → Nat :=
-- fun n => n + 1
```

For a definition made by pattern matching, `#print equations ident` (or
the shorter `#print eqns ident`) shows the equations Lean derived from the
match — often more informative than the compiled definition itself:

```lean4
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#print equations fib
-- equations:
-- @[backward_defeq] theorem fib.eq_1 : fib 0 = 0
-- @[backward_defeq] theorem fib.eq_2 : fib 1 = 1
-- @[backward_defeq] theorem fib.eq_3 : ∀ (n : Nat), fib n.succ.succ = fib n + fib (n + 1)
```

`#reduce`
--------------------------------------------------------------------------------

Like `#eval`, `#reduce e` computes a value for `e` — but the two get there
very differently, and that difference is the point.

`#eval` *compiles* `e` to executable code and runs it; the result is then
printed via `ToExpr`/`Repr`/`ToString` (see above), so anything without
one of those instances can't be displayed — functions included. `#reduce`
instead *unfolds* `e` using Lean's definitional-equality reduction
rules — the same notion of "equal by computation" the type checker itself
uses — and prints whatever term comes out, with no compilation step and no
printing instance required. That lets `#reduce` show things `#eval`
refuses to, such as a function:

```lean4
#reduce (fun x : Nat => x + 1)
-- fun x => x.succ
```

On closed, fully computable terms the two usually agree:

```lean4
#reduce succ 3
-- 4
```

`#reduce` is the right tool when you want to inspect *how* an expression
reduces — for example while debugging a definitional-equality mismatch —
rather than just its final value. It has no side effects (an `IO` action
given to `#reduce` is not run), and because unfolding proofs and type
annotations is expensive and rarely useful, it skips both by default;
`#reduce (proofs := true) e` and `#reduce (types := true) e` opt back in.
For everyday "what does this evaluate to?" questions, `#eval` remains the
better default: it's much faster, and its output is usually easier to read.

`#synth`
--------------------------------------------------------------------------------

`#synth C` runs type class resolution for `C` and reports which instance
it finds, or fails if none does. It's the tool for checking *why* `#eval`,
`#check`, or `+` succeeded or failed above.

`Nat` has all three printing instances from the "Printing the result"
section:

```lean4
#eval 0
-- 0

#check 0
-- 0 : Nat

#synth Lean.ToExpr Nat
-- Lean.instToExprNat

#synth Repr Nat
-- instReprNat

#synth ToString Nat
-- instToStringNat
```

Alternatively, try the type class API directly:

```lean4
#eval ToString.toString 0
-- "0"
```

`Nat → Nat` has none of them, which is exactly why `succ` couldn't be
`#eval`'d earlier:

```lean4
#eval succ
-- Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
--   Nat → Nat

#check succ
-- succ (n : Nat) : Nat

#check @succ
-- succ : Nat → Nat

#synth Lean.ToExpr (Nat → Nat)
-- failed to synthesize
--   Lean.ToExpr (Nat → Nat)

#synth Repr (Nat → Nat)
-- failed to synthesize
--   Repr (Nat → Nat)

#synth ToString (Nat → Nat)
-- failed to synthesize
--   ToString (Nat → Nat)

#eval ToString.toString succ
-- failed to synthesize instance of type class
--   ToString (Nat → Nat)
```

And the same trick explains the `HAdd` failure from the very first such
example in this file:

```lean4
#eval 1 + "Hello"
-- failed to synthesize instance of type class
--   HAdd Nat String ?m.1

#synth HAdd Nat String String
-- failed to synthesize
--   HAdd Nat String String
```

`#guard_msgs`
--------------------------------------------------------------------------------

`#guard_msgs` runs the command that follows it and checks that the
messages it produces (info, warnings, errors) match an expected message
given in a doc comment placed right above it. It turns an example like the
failing `#eval`s earlier in this file into an automated test: if the
message Lean produces ever changes, `#guard_msgs` itself fails, flagging
that this file is out of date.

```lean4
/-- info: 2 -/
#guard_msgs in
#eval 1 + 1

/--
error: Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Nat → Nat
-/
#guard_msgs in
#eval succ
```

By default, `#guard_msgs` checks *every* message and requires an exact
match (whitespace normalized, order preserved). A filter narrows what is
checked: `#guard_msgs (warning) in cmd` checks only warnings and silently
drops everything else, while `#guard_msgs (drop warning) in cmd` checks
everything *but* warnings. This is handy when a command is expected to
also emit an unrelated linter warning that isn't the point of the example.
