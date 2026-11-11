import Mathlib

/-!
TODO:
  - (ℕ, +, 0) is an (additive) monoid,
  - ({α β} [Monad m] α → m β, >==>, pure) is a monoid,
    ⚠️ update: nope, that doesn't work like that unless β = α.
    What we have here is a category.
  - for any n, (Equiv.Perm (Fin n), Equiv.trans, Equiv.refl) is a monoid.

-/

/-!
The definition of `Monoid` reveals that to declare an instance of `Monoid M`,
one has to provide an internal operation binary function `mul : M → M → M`
and an term `one : M` and provide the profs that `mul` is associative
and that `one` is neutral on the left and on the right. Once this instance
is declared, `*` and `1` can be used to denote `mul` and `one`.
-/

#print Monoid
-- class Monoid.{u} (M : Type u) : Type u
-- number of parameters: 1
-- ...
-- fields:
--   [...].mul : M → M → M
--   [...].mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c)
--   [...].one : M
--   [...].one_mul : ∀ (a : M), 1 * a = a
--   [...].mul_one : ∀ (a : M), a * 1 = a
-- ...

/-!
`AddMonoid` is a similar type class, but the internal operation is denoted
`+` and the neutral element `0`  (usually, that's the preferred
convent when the operation is actually commutative).
-/

#print AddMonoid
-- class AddMonoid.{u} (M : Type u) : Type u
-- number of parameters: 1
-- ...
-- fields:
--   [...].add : M → M → M
--   [...].add_assoc : ∀ (a b c : M), a + b + c = a + (b + c)
--   [...].zero : M
--   [...].zero_add : ∀ (a : M), 0 + a = a
--   [...].add_zero : ∀ (a : M), a + 0 = a
--   [...].nsmul : ℕ → M → M
-- ...

/-!
Note how Mathlib requires that you provide an extra function,
`nsmul: ℕ → M → M` that represents the sum of `n` terms `x + x + ... + x`
(after the creation of the instance that can be denoted `n · x`).
Of course there is a generic, recursive implementation that exist
for every type that has a zero and support addition: it's called `nsmulRec`
and we're going to use this one.

```lean4
def nsmulRec [Zero M] [Add M] : Nat → M → M
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a
```
-/

#check nsmulRec
-- nsmulRec.{u_1} {M : Type u_1} [Zero M] [Add M] : ℕ → M → M

/-!
Natural numbers
--------------------------------------------------------------------------------
-/

instance : AddMonoid ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  nsmul := nsmulRec

/-!
That's all their is to it! Now we can use in `ℕ` all theorems proven for
additive monoids, such as
-/

theorem zero_add_zero {M} [AddMonoid M] : (0 : M) + (0 : M) = (0 : M) := by
  apply AddMonoid.add_zero

theorem Nat_zero_add_zero : 0 + 0 = 0 := by
  apply zero_add_zero

/-!
Lets prove the `Nat` version of `add_assoc`, `zero_add` and `add_zero` by hand!
-/

#check Nat.add_zero
-- Nat.add_zero (n : ℕ) : n + 0 = n

#print Nat.add
-- @[instance_reducible] protected def Nat.add : ℕ → ℕ → ℕ :=
-- fun x x_1 => Nat.brecOn (motive := fun x => ℕ → ℕ) x_1 Nat.add._f x

/-!
The source actually is:

```lean4
@[extern "lean_nat_add", instance_reducible]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

-/

theorem Nat_add_zero (n : ℕ) : n + 0 = n := by
  rw [HAdd.hAdd]
  rw [instHAdd]
  simp only
  rw [Add.add]
  rw [instAddNat]
  simp only
  rw [Nat.add]

/-!
A cleaned-up version
-/
theorem Nat_add_zero' (n : ℕ) : n + 0 = n := by
  simp_rw [HAdd.hAdd, Add.add, Nat.add]

/-!
The `simp` tactic actually one-shots of course (using `Nat.add_zero`)!
-/
theorem Nat_add_zero'' (n : ℕ) : n + 0 = n := by
  simp

/-!
`Nat.zero_add` is a bit trickier since addition for natural numbers is defined
by a recursion on the right operand. And even then, at the moment we're going
to be stuck since we need associativity. So we're going to cheat and used
the already existing proof of associativity (but we'll prove it later).
-/

#check Nat.zero_add
-- Nat.zero_add (n : ℕ) : 0 + n = n

#check Nat.add_assoc
-- Nat.add_assoc (n m k : ℕ) : n + m + k = n + (m + k)

/-!
Let's prove the theorem recursively. This is exactly like defining a function
recursively (termination matters! Here we are using structural recursion so
that obvious)
-/

theorem Nat_zero_add (n : ℕ) : 0 + n = n := by
  match n with
  | 0 =>
    apply Nat_zero_add_zero
  | n + 1 =>
    have h : 0 + n + 1 = 0 + (n + 1) := Nat.add_assoc 0 n 1
    rw [<- h] -- or use `h.symm` or use `.symm` in the proof above.
    rw [Nat_zero_add n]

/-!
The version for the more mathematically inclined, with an explicit induction:
-/

theorem Nat_zero_add' (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => apply Nat_zero_add_zero
  | succ n ih =>
    have h : 0 + n + 1 = 0 + (n + 1) := Nat.add_assoc 0 n 1
    rw [<- h] -- or use `h.symm` or use `.symm` in the proof above.
    rw [ih]

/-!
Let's prove associativity of the addition now.
-/

#check Nat.add_assoc
-- Nat.add_assoc (n m k : ℕ) : n + m + k = n + (m + k)

theorem Nat_add_assoc_sorry (n m k : ℕ) : n + m + k = n + (m + k) := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    have h1 : n + m + (k + 1) = (n + m + k) + 1 := by sorry
    have h2 : (n + m + k) + 1 = (n + (m + k)) + 1 := by sorry
    have h3 : (n + (m + k)) + 1 = n + (m + k + 1) := by sorry
    have h4 :  n + (m + k + 1) = n + (m + (k + 1)) := by sorry
    rw [h1, h2, h3, h4]

theorem Nat_add_assoc (n m k : ℕ) : n + m + k = n + (m + k) := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    have h1 : n + m + (k + 1) = (n + m + k) + 1 := by
      simp only [HAdd.hAdd, Add.add, Nat.add]
    have h2 : (n + m + k) + 1 = (n + (m + k)) + 1 := by
      simp only [ih]
    have h3 : (n + (m + k)) + 1 = n + (m + k + 1) := by
      simp only [HAdd.hAdd, Add.add, Nat.add]
    have h4 :  n + (m + k + 1) = n + (m + (k + 1)) := by
      simp only [HAdd.hAdd, Add.add, Nat.add]
    rw [h1, h2, h3, h4]

theorem Nat_add_assoc' (n m k : ℕ) : n + m + k = n + (m + k) := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    calc n + m + (k + 1)
      _ =  (n + m + k) + 1 := by simp only [HAdd.hAdd, Add.add, Nat.add]
      _ = (n + (m + k)) + 1 := by simp only [ih]
      _ = n + (m + k + 1) := by simp only [HAdd.hAdd, Add.add, Nat.add]
      _ = n + (m + (k + 1)) := by simp only [HAdd.hAdd, Add.add, Nat.add]

macro "unfold_add" : tactic => `(tactic| simp only [HAdd.hAdd, Add.add, Nat.add])

theorem Nat_add_assoc'' (n m k : ℕ) : n + m + k = n + (m + k) := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    calc n + m + (k + 1)
      _ =  (n + m + k) + 1 := by unfold_add
      _ = (n + (m + k)) + 1 := by simp only [ih]
      _ = n + (m + k + 1) := by unfold_add
      _ = n + (m + (k + 1)) := by unfold_add

theorem Nat_add_assoc''' (n m k : ℕ) : n + m + k = n + (m + k) := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    calc n + m + (k + 1)
      _ =  (n + m + k) + 1 := by grind
      _ = (n + (m + k)) + 1 := by grind
      _ = n + (m + k + 1) := by grind
      _ = n + (m + (k + 1)) := by grind



/-!
(Lawful) Monads
--------------------------------------------------------------------------------
-/

#print Monad
-- class Monad.{u, v} (m : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- ...
--   [...].pure : {α : Type u} → α → m α
--   [...].bind : {α β : Type u} → m α → (α → m β) → m β
-- ...

/-!
Instead of relying only on `pure` and `bind`, the `LawfulMonad` type class in
Lean actually requires a `id_map` property of `Functor.map` (operator `<$>`)
and the proof that defines `<$>` in terms of `pure` and `bind`, which makes
the `id_map` property equivalent to the classic `bind_pure`.
-/

#print LawfulMonad
-- class LawfulMonad.{u, v} (m : Type u → Type v) [Monad m] : Prop
-- number of parameters: 2
-- parents:
--   LawfulMonad.toLawfulApplicative : LawfulApplicative m
-- fields:
--   -- Note: `f <$> x` is `x >>= fun a => pure (f a)`
--   [...].id_map : ∀ {α : Type u} (x : m α), id <$> x = x
--   [...].bind_pure_comp : ∀ {α β : Type u} (f : α → β) (x : m α),
      -- (do
      --     let a ← x
      --     pure (f a)) =
      --   f <$> x
--   [...].pure_bind : ∀ {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
--   [...].bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
--       x >>= f >>= g = x >>= fun x => f x >>= g

#check bind_pure
-- bind_pure.{u_1, u_2}
-- {m : Type u_1 → Type u_2} {α : Type u_1}
-- [Monad m] [LawfulMonad m]
-- (x : m α) : x >>= pure = x

/-!
So what really matters for us in lawful monads are `pure_bind`, `bind_pure`
and `bind_assoc`.
-/

/-!
The `Bind.kleisliRight` function is associate to the "fish" `>=>` operator.
-/

#print Bind.kleisliRight
-- def Bind.kleisliRight.{u, u_1, u_2} : {α : Type u} →
--  {m : Type u_1 → Type u_2} → {β γ : Type u_1} → [Bind m] → (α → m β) → (β → m γ) → α → m γ :=
-- fun {α} {m} {β γ} [Bind m] f₁ f₂ a => f₁ a >>= f₂

/-!
Let's prove alternate versions of the main monadic laws, based on the fish
operator and pure instead of bind and pure.
-/
