import Mathlib

/-!
Rewrite rules
================================================================================
-/

/-!
eq + goal => rewrite
-/

/-!
eq in the wrong way + goal => rewrite <-
-/

/-!
rw is actually rewrite with an attempt to close trivial goals afterwards with
a weak version rfl (only the definition marked as @[reducible] are expanded:
with_reducible rfl).

(NOBODY uses rewrite)
-/

/-!
sequences of rewrites, hover/cursor in between.
-/

/-!
target assumption, assumption, the goal, everything
-/

/-!
rewrite definitions (def -> def eq ?) and local definitions
(let won't work, use set ... with h ?);
-/

/-!
nth_rw, repeat (carpet bombing), conv
-/

/-!
rw doesn't work under "binders" (fun abstraction? Yes: a construction that
introduces a new variable)
-/

/-!
conv can help for targetting AND working under binders.
-/

/-!
simp in general, how that works, what simp [...] does (extend the simp set).
-/

/-!
simp only [...] and bare simp only (only applies a small set of reductions,
beta, zeta, iota, proj, etc. The classic rules of lambda calculus, except
for delta-reduction (unfolding a function definition))
-/

/-!
Use `simp?`, then transform your carpet bombing proof into a chiseled one!
-/

/-!
simp_rw ; sequential application of simp only, not "set" of rewrite rules.
Can examine the state between stages (cursor)
-/

/-!
A simple example: with `simp only`, the order of the rules is irrelevant.
-/

example (a b : Nat) : a + 0 + 0 * b = a := by
  simp only [Nat.add_zero, Nat.zero_mul]

/-!
With `simp_rw`, `Nat.add_zero` turns `a + 0 + 0 * b` into `a + 0 * b`,
then `Nat.zero_mul` produces `a + 0`... and nobody is left to remove the
new `+ 0`. Goal left: `a + 0 = a`.
-/

example (a b : Nat) : a + 0 + 0 * b = a := by
  simp_rw [Nat.add_zero, Nat.zero_mul]
  sorry -- ⊢ a + 0 = a

/-! Fix 1: repeat the rule. -/
example (a b : Nat) : a + 0 + 0 * b = a := by
  simp_rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero]

/-! Fix 2: reorder, so that one `Nat.add_zero` pass removes both `+ 0`. -/
example (a b : Nat) : a + 0 + 0 * b = a := by
  simp_rw [Nat.zero_mul, Nat.add_zero]

/-!
For example, with `simp only` in this example the order of you
added rewrite rules doesn't matter; you can name
`sInf_empty` before you name `Set.image_empty`.
-/

theorem map_top {α β} [CompleteLinearOrder α]  [CompleteLinearOrder β]
    (f : α → β)
    (hf : ∀ (s : Set α), f (sInf s) = sInf (f '' s)) :
    f ⊤ = ⊤ := by
  specialize hf ∅
  simp only [sInf_empty, Set.image_empty] at hf
  assumption

/-!
But if you use this order with `simp_rw`, you will need to add an
extra `sInf_empty` at the end. Or you change change the order in which
you name the rewrite rules, perform the `Set.image_empty` rewrite first,
which allows you to perform both `sInf_empty` simplifications in one
go afterwards.
-/

theorem map_top' {α β} [CompleteLinearOrder α]  [CompleteLinearOrder β]
    (f : α → β)
    (hf : ∀ (s : Set α), f (sInf s) = sInf (f '' s)) :
    f ⊤ = ⊤ := by
  specialize hf ∅
  simp_rw [sInf_empty, Set.image_empty, sInf_empty] at hf
  assumption

theorem map_top'' {α β} [CompleteLinearOrder α]  [CompleteLinearOrder β]
    (f : α → β)
    (hf : ∀ (s : Set α), f (sInf s) = sInf (f '' s)) :
    f ⊤ = ⊤ := by
  specialize hf ∅
  simp_rw [Set.image_empty, sInf_empty] at hf
  assumption
