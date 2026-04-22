
```lean4
import Mathlib
```

# Reflexivity

The simplest method that you can expect to prove some equality is to invoke
the reflexivity of equality:


```lean4
#check rfl
-- rfl.{u} {α : Sort u} {a : α} : a = a
```

Note that `rfl` is function but its only argument is implicit and will be
inferred from the context. So syntactically, it can be used as a constant:


```lean4
theorem one_eq_one : 1 = 1 := rfl
```

Of course we could be more explicit (but don't need to):

```lean4
theorem one_eq_one' : 1 = 1 := rfl (a := 1)

/-
Reflexivity can also be used as a tactic (usually as a frament of larger proofs)
-/

theorem one_eq_one'' : 1 = 1 := by rfl


theorem n_eq_n : ∀ (n : ℕ), n = n := by
  intro n
  rfl -- Actually intro works "up to rfl" so this rfl is not necessary
```

This method seems to be really limited, but Lean will actually perform some
simplifications (*reductions*) before the comparison of the left-hand side
and the right-hand side. Therefore the scope of this method is actually
wider than you may think. When `rfl` succeeds, the lhs and rhs of the
equality are *definitionally equal* (i.e. equal *by definition*).

To begin with, Lean can seamlessly rename some bound variables (α-conversion),
so, we can for example prove

```lean4
example : (fun (x y : ℕ) => x + y) = (fun (a b : ℕ) => a + b) := rfl
```

Global constants and local variables are substituted in expressions via
δ-reduction:

```lean4
def fortyTwo := 42

#reduce fortyTwo
-- 42

example : fortyTwo = 42 := rfl

#reduce (let three := 3; three)
-- 3

example : (let three := 3; three) = 3 := rfl
```

That also works for functions:

```lean4
def next := Nat.succ

#reduce next
-- Nat.succ

example : next = Nat.succ := rfl
```

β-conversion is the simplification of function application:

```lean4
example : (fun _ => 42) 100 = 42 := rfl
```

ι-reduction simplifies pattern matching expressions:

```lean4
#reduce (match true with | false => 0 | true => 1)
-- 1

example : (match true with | false => 0 | true => 1) = 1 := rfl
```

Now of course, all theses reductions (and some others) can be combine
(multiple times if needed). For example, given the definition of
the global function

```lean4
def not' := fun (b : Bool) =>
  match b with
  | false => true
  | true => false
```

By application of δ-reduction for `not'`, then β-reduction and finally
ι-reduction, we can prove that

```lean4
example : not' true = false := rfl
```
