/-!
Interactive Commands
================================================================================

Source: [Interacting with Lean
](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/)

-/

/-!
`#eval`
--------------------------------------------------------------------------------
-/

/-!
The `#eval` commands can do a lot of simple things
-/

/-!
Display expressions:
-/

#eval 1 + 1
-- 2

/-!
Execute some IO actions:
-/

#eval IO.println "Hello world!"
-- Hello word!

/-!
Evaluate some propositions
-/
#eval 0 ≤ 1
-- true

/-!
One-liner are not required, complex expressions are ok too:
-/

#eval
  let name := "L∃∀N"
  let greet := fun name? : Option String =>
    let name := match name? with
    | some name => name
    | none => "Odysseus"
    s!"Hello {name}!"
  greet name
-- "Hello L∃∀N!"

/-!
Everything is typechecked beforehand:
-/

#eval 1 + "Hello"
-- failed to synthesize instance of type class
--   HAdd Nat String ?m.1

-- Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

/-!
`#eval e` computes `e`, then needs some way to print the result as text.
It tries, in order to use a `ToExpr`, `Repr`, or `ToString` instance,
if they exist; otherwise it fails

**TODO** details about the 3 options, what they mean, what they are used for.

For example:

-/

def succ (n : Nat) : Nat := n + 1

#eval succ
-- could not synthesize a `Repr` or `ToString` instance for type
--   Nat → Nat

/-!

### Monad support

`IO` is actually a special case for a larger category supported by `#eval`.

If `e : m τ` for some monad `m`, `#eval` also needs to know how to run that monad,
independent of how it displays the result.
If `e` is a monadic value of type `m τ`,
then the command tries to adapt the monad `m`
to one of the monads that `#eval` supports, which include `IO`, `CoreM`, `MetaM`,
`TermElabM`, and `CommandElabM`.
Users can define `MonadEval` instances to extend the list of supported monads.
-/

/-!
### Proposition support

The expressions `0 = 0` or `0 < 1` `#eval` to booleans
-/

#eval 0 = 0
-- true

#eval 0 ≤ 1
-- true

/-!
but they are not booleans, they are propositions. These examples work with
`#eval` because the are decidable propositions, whose truth value
(a boolean) can systematically computed by a verified algorithm.
`#eval` automatically does that ; explicitly, we could have done:
-/

#eval decide (0 = 0)
-- true

#eval decide (0 < 1)
-- true


/-!
If Lean doesn't manage to determine that your proposition is decidable,
`#eval` will fail
-/

#eval ∀ x y z n : Nat, n > 2 ∧ x > 0 ∧ y > 0 ∧ z > 0 → x ^ n + y ^ n ≠ z ^ n

/-!
The truth value of the Last Fermat theorem cannot be evaluated since we
have not been through the (very complex task) of declaring to Lean a
verified proof of it.
-/

/-!
`#check`
--------------------------------------------------------------------------------


The `#check e` command verifies that the expression `e` can be correctly
type checked and display its type, or throws an error.
-/

#check 0
-- 0 : Nat

#check 0 + "Hello!"
-- failed to synthesize instance of type class
--   HAdd Nat String ?m.5

-- Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

/-!
`#check e` does not *reduce* your expression `e`:
-/

#check 1 + 1
-- 1 + 1 : Nat

/-!
It can still simplify your expression somehow if for example you use parentheses
that are not needed when you are unsure of the operator precedences and
associativity properties, or you use non-standard spacing and indentation
-/

#check 1+1  +  1
-- 1 + 1 + 1 : Nat

#check (1 + 1) + 1
-- 1 + 1 + 1 : Nat

#check 1 + (1 + 1)
-- 1 + (1 + 1) : Nat

/-!
The `#check e` command doesn't need `e` to be displayed as text.
For example, this works perfectly:
-/

#check succ
-- succ (n : Nat) : Nat

/-!
Extra examples
-/

#check 0 = 0
-- 0 = 0 : Prop

#check decide (0 = 0)
-- decide (0 = 0) : Bool

#check 0 == 0
-- 0 == 0 : Bool

#check 0 < 1
-- 0 ≤ 1 : Prop

#check decide (0 < 1)
-- decide (0 = 1) : Bool

#check Ord.compare 0 1 == Ordering.lt
-- compare 0 1 == Ordering.lt : Bool



/-!
`#print`
--------------------------------------------------------------------------------
-/

/-!
**TODO**. Example with `succ` and maybe another global constant? I should
have defined `name` as a global from the start with the `"L∃∀N"` value
and used it in `#eval`. And then here, reuse it to print it.
-/

/-!
`#reduce`
--------------------------------------------------------------------------------
-/

/-!
**TODO**. Contrast/compare with `#eval`. Which one is good for what?
-/


/-!
`#synth`
--------------------------------------------------------------------------------
-/

/-!
**TODO**. Simple example that connects with what we have seen before:
check for `ToString`, `Repr`, `ToExpr` on one hand, and `Decidable` on
the other hand and do that with the previous examples of this document.
-/

/-!
#guard_msgs
--------------------------------------------------------------------------------
-/

/-!
**TODO**
-/
