
```lean4
import Mathlib
```

Rewrite rules
================================================================================

The `rewrite` tactic uses an equality to perform a substitution:

```lean4
example {n : ℕ} (hn : n = 1) : n + 1 = 2 := by
  rewrite [hn] -- new goal: ⊢ 1 + 1 = 2
  rfl
```

The `rfl` tactic check if the left-hand side and the right-hand are
**definitionally equal**, which is true.

The `rewrite` tactic is rarely used; instead one uses `rw`, which has the
same syntax but applies automatically a weak[^1] version of `rfl` to try and
close the goal automatically.

[^1]: It applies `with_reducible rfl`, which only expands definition marked
explicitly as `@[reducible]`. By default, definitions are only semi-reducible.

```lean4
example {n : ℕ} (hn : n = 1) : n + 1 = 2 := by
  rw [hn] -- ⊢ 1 + 1 = 2, which is automatically closed.
```

By default, rewrites use an equality `a = b` to transform `a` into `b`.
We can use the symmetry of the equality if we want to perform the
converse substitution:

```lean4
#check Eq.symm
-- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a

example {n : ℕ} (hn : 1 = n) : n + 1 = 2 := by
  rw [hn.symm]
```

But `rw` has a simpler syntax to do that:

```lean4
example {n : ℕ} (hn : 1 = n) : n + 1 = 2 := by
  rw [← hn]
```

The equality can be parametrized, i.e. returned by a function.
For example, the theorem `Nat.add_zero` and `Nat.mul_one` provide
equalities given a natural number `n`:

```lean4
#check Nat.add_zero
-- Nat.add_zero (n : ℕ) : n + 0 = n

#check Nat.mul_one
-- Nat.mul_one (n : ℕ) : n * 1 = n
```

So we can use them to prove that `(n + 0) * 1 = n`:

```lean4
example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.add_zero n] -- ⊢ n * 1 = n
  rw [Nat.mul_one n]  -- Goals accomplished!
```

Equivalently:

```lean4
example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.mul_one (n + 0)] -- ⊢ n + 0 = n
  rw [Nat.add_zero n]      -- Goals accomplished!
```

You can also use the hole `_` argument to let Lean try to infer from the
context what the argument of the theorem should be:

```lean4
example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.add_zero _] -- ⊢ n * 1 = n
  rw [Nat.mul_one _]  -- Goals accomplished!

example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.mul_one _]  -- ⊢ n + 0 = n
  rw [Nat.add_zero _] -- Goals accomplished!
```

Equivalently, don't mention the argument at all:

```lean4
example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.add_zero] -- ⊢ n * 1 = n
  rw [Nat.mul_one]  -- Goals accomplished!

example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.mul_one]  -- ⊢ n + 0 = n
  rw [Nat.add_zero] -- Goals accomplished!
```

These sequence of rewrites can be rewritten in a terser form:

```lean4
example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.add_zero, Nat.mul_one] -- Goals accomplished!

example {n : ℕ} : (n + 0) * 1 = n := by
  rw [Nat.mul_one, Nat.add_zero] -- Goals accomplished!
```

You can still see the stage of the proof if you put your cursor between
two terms between the brackets. It's even more obvious with the following
indendation:

```lean4
example {n : ℕ} : (n + 0) * 1 = n := by
  rw [
    Nat.add_zero, -- ⊢ n * 1 = n
    Nat.mul_one   -- Goals accomplished!
  ]

example {n : ℕ} : (n + 0) * 1 = n := by
  rw [
    Nat.mul_one, -- ⊢ n + 0 = n
    Nat.add_zero -- Goals accomplished!
  ]
```

By default a rewrite will target the goal; tt's possible
target an assumption instead with the syntax `rw [...] at ...` syntax:

```lean4
example {n : ℕ} (hn : n + 0 = 1) : n + 1 = 2 := by
  rw [Nat.add_zero] at hn -- hn : n = 1
  rw [hn]                 -- Goals accomplished!
```

The bare `rw` is actually a shortcurt for `rw ... at ⊢` (the turnstile
symbol `⊢` can be typed as the sequence `\|-`, slash-pipe-minus):

```lean4
example {n : ℕ} (hn : n + 0 = 1) : n + 1 = 2 := by
  rw [Nat.add_zero] at hn -- hn : n = 1
  rw [hn] at ⊢            -- Goals accomplished!
```

You can also try and perform some rewriting at several places at once:

```lean4
example {n : ℕ} (hn : n + 0 = 1) : (n + 1) + 0 = 2 := by
  rw [Nat.add_zero] at hn ⊢ -- hn : n = 1, ⊢ n + 1 = 2
  rw [hn]                   -- Goals accomplished!
```

You can even try to target all assumptions and the goal at once:

```lean4
example {n : ℕ} (hn : n + 0 = 1) : (n + 1) + 0 = 2 := by
  rw [Nat.add_zero] at * -- hn : n = 1, ⊢ n + 1 = 2
  rw [hn]                -- Goals accomplished!
```

You can even go crazy and try to rewrite all targets at each step:

```lean4
example {n : ℕ} (hn : n + 0 = 1) : (n + 1) + 0 = 2 := by
  rw [Nat.add_zero, hn] at * -- Goals accomplished!
```

You can rewrite global definitions:

```lean4
def answer := 42

example : answer + 1 = 43 := by
  rw [answer]
```

That works in the simples cases but often, you need to actually
using the generated equations `.eq_def` associated to the definition:

```lean4
#print answer.eq_def
-- @[backward_defeq] theorem answer.eq_def : answer = 42 :=
-- Eq.refl answer

example : answer + 1 = 43 := by
  rw [answer.eq_def]
```

When your definition is a pattern match, several equations are generated:

```lean4
def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n


#check fact.eq_def
-- fact.eq_def (x✝ : ℕ) :
--   fact x✝ =
--     match x✝ with
--     | 0 => 1
--     | n.succ => (n + 1) * fact n

#check fact.eq_1
-- fact.eq_1 : fact 0 = 1

#check fact.eq_2
-- fact.eq_2 (n : ℕ) : fact n.succ = (n + 1) * fact n

example (n : ℕ) : fact (n + 2) = (n + 2) * (n + 1) * fact n := by
  rw [fact] -- ⊢ (n + 1 + 1) * fact (n + 1) = (n + 2) * (n + 1) * fact n
  rw [fact] -- ⊢ (n + 1 + 1) * ((n + 1) * fact n) = (n + 2) * (n + 1) * fact n
  grind
```

Which is equivalent to the more targetted:

```lean4
example (n : ℕ) : fact (n + 2) = (n + 2) * (n + 1) * fact n := by
  rw [fact.eq_2 (n + 1)] -- ⊢ (n + 1 + 1) * fact (n + 1) = (n + 2) * (n + 1) * fact n
  rw [fact.eq_2 n]       -- ⊢ (n + 1 + 1) * ((n + 1) * fact n) = (n + 2) * (n + 1) * fact n
  grind
```

If you don't like `grind` and wish to conclude the proof with elementary rewrites:

```lean4
example (n : ℕ) : fact (n + 2) = (n + 2) * (n + 1) * fact n := by
  rw [fact.eq_2 (n + 1)] -- ⊢ (n + 1 + 1) * fact (n + 1) = (n + 2) * (n + 1) * fact n
  rw [fact.eq_2 n]       -- ⊢ (n + 1 + 1) * ((n + 1) * fact n) = (n + 2) * (n + 1) * fact n
  have hn : n + 1 + 1 = n + 2 := by rfl
  rw [hn]
  rw [Nat.mul_assoc]
```

The compact version where we "inline" the intermediate lemma:

```lean4
example (n : ℕ) :  fact (n + 2) = (n + 2) * (n + 1) * fact n := by
  rw [fact, fact, show n + 1 + 1 = n + 2 from by rfl, Nat.mul_assoc]
```

Rewrite won't work with local definition with `let`, which do not generate
equations. You have to state the equation yourself and prove it (which is
easy since it holds by definition, so `rfl` works!)

```lean4
example (m n : ℕ) (hmn : m + n = 1) : (m + n) ^ 2 + (m + n) = 2 := by
  let p := m + n
  have hp : m + n = p := by rfl
  rw [hp] at hmn ⊢
  rw [hmn]
  rfl
```

Alternatively, you can use `set p := ... with hp` that will automatically
perform the rewrite for all occurrences of the right-hand side in this
definition:

```lean4
example (m n : ℕ) (hmn : m + n = 1) : (m + n) ^ 2 + (m + n) = 2 := by
  set p := m + n with hp
  rw [hmn]
  rfl
```

--------------------------------------------------------------------------------

nth_rw, repeat (carpet bombing), conv

rw doesn't work under "binders" (fun abstraction? Yes: a construction that
introduces a new variable)

conv can help for targetting AND working under binders.

--------------------------------------------------------------------------------

simp in general, how that works, what simp [...] does (extend the simp set).

simp only [...] and bare simp only (only applies a small set of reductions,
beta, zeta, iota, proj, etc. The classic rules of lambda calculus, except
for delta-reduction (unfolding a function definition))

Use `simp?`, then transform your carpet bombing proof into a chiseled one!

simp_rw ; sequential application of simp only, not "set" of rewrite rules.
Can examine the state between stages (cursor)

A simple example: with `simp only`, the order of the rules is irrelevant.

```lean4
example (a b : Nat) : a + 0 + 0 * b = a := by
  simp only [Nat.add_zero, Nat.zero_mul]
```

With `simp_rw`, `Nat.add_zero` turns `a + 0 + 0 * b` into `a + 0 * b`,
then `Nat.zero_mul` produces `a + 0`... and nobody is left to remove the
new `+ 0`. Goal left: `a + 0 = a`.

```lean4
example (a b : Nat) : a + 0 + 0 * b = a := by
  simp_rw [Nat.add_zero, Nat.zero_mul]
  sorry -- ⊢ a + 0 = a

/-! Fix 1: repeat the rule. -/
example (a b : Nat) : a + 0 + 0 * b = a := by
  simp_rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero]

/-! Fix 2: reorder, so that one `Nat.add_zero` pass removes both `+ 0`. -/
example (a b : Nat) : a + 0 + 0 * b = a := by
  simp_rw [Nat.zero_mul, Nat.add_zero]
```

For example, with `simp only` in this example the order of you
added rewrite rules doesn't matter; you can name
`sInf_empty` before you name `Set.image_empty`.

```lean4
theorem map_top {α β} [CompleteLinearOrder α]  [CompleteLinearOrder β]
    (f : α → β)
    (hf : ∀ (s : Set α), f (sInf s) = sInf (f '' s)) :
    f ⊤ = ⊤ := by
  specialize hf ∅
  simp only [sInf_empty, Set.image_empty] at hf
  assumption
```

But if you use this order with `simp_rw`, you will need to add an
extra `sInf_empty` at the end. Or you change change the order in which
you name the rewrite rules, perform the `Set.image_empty` rewrite first,
which allows you to perform both `sInf_empty` simplifications in one
go afterwards.
