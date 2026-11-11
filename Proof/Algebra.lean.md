
```lean4
import Mathlib
```

TODO:
  - (ℕ, +, 0) is an (additive) monoid,
  - ({α β} [Monad m] α → m β, >==>, pure) is a monoid,
    ⚠️ update: nope, that doesn't work like that unless β = α.
    What we have here is a category. Arf, we have a monoid "object" which is
    a generalisation of monoid ... need to dig more there.
  - for any n, (Equiv.Perm (Fin n), Equiv.trans, Equiv.refl.
    Arf, what matters here is that we have a groupoid.


TODO: deemphasize the Monoid stuff. Focus on the 3 properties we want to prove,
then afterwards show that it provides a Monoid instance and that we can use
this to specialize theorems that are valid for every Monoid.


The definition of `Monoid` reveals that to declare an instance of `Monoid M`,
one has to provide an internal operation binary function `mul : M → M → M`
and an term `one : M` and provide the profs that `mul` is associative
and that `one` is neutral on the left and on the right. Once this instance
is declared, `*` and `1` can be used to denote `mul` and `one`.

```lean4
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
```

`AddMonoid` is a similar type class, but the internal operation is denoted
`+` and the neutral element `0`  (usually, that's the preferred
convent when the operation is actually commutative).

```lean4
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
```

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

```lean4
#check nsmulRec
-- nsmulRec.{u_1} {M : Type u_1} [Zero M] [Add M] : ℕ → M → M
```

Natural numbers
--------------------------------------------------------------------------------

```lean4
instance : AddMonoid ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  nsmul := nsmulRec
```

That's all their is to it! Now we can use in `ℕ` all theorems proven for
additive monoids, such as

```lean4
theorem zero_add_zero {M} [AddMonoid M] : (0 : M) + (0 : M) = (0 : M) := by
  apply AddMonoid.add_zero

theorem Nat_zero_add_zero : 0 + 0 = 0 := by
  apply zero_add_zero
```

Lets prove the `Nat` version of `add_assoc`, `zero_add` and `add_zero` by hand!

```lean4
#check Nat.add_zero
-- Nat.add_zero (n : ℕ) : n + 0 = n

#print Nat.add
-- @[instance_reducible] protected def Nat.add : ℕ → ℕ → ℕ :=
-- fun x x_1 => Nat.brecOn (motive := fun x => ℕ → ℕ) x_1 Nat.add._f x
```

The source actually is:

```lean4
@[extern "lean_nat_add", instance_reducible]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```


```lean4
theorem Nat_add_zero (n : ℕ) : n + 0 = n := by
  rw [HAdd.hAdd]
  rw [instHAdd]
  simp only
  rw [Add.add]
  rw [instAddNat]
  simp only
  rw [Nat.add]
```

A cleaned-up version

```lean4
theorem Nat_add_zero' (n : ℕ) : n + 0 = n := by
  simp_rw [HAdd.hAdd, Add.add, Nat.add]
```

The `simp` tactic actually one-shots of course (using `Nat.add_zero`)!

```lean4
theorem Nat_add_zero'' (n : ℕ) : n + 0 = n := by
  simp
```

`Nat.zero_add` is a bit trickier since addition for natural numbers is defined
by a recursion on the right operand. And even then, at the moment we're going
to be stuck since we need associativity. So we're going to cheat and used
the already existing proof of associativity (but we'll prove it later).

```lean4
#check Nat.zero_add
-- Nat.zero_add (n : ℕ) : 0 + n = n

#check Nat.add_assoc
-- Nat.add_assoc (n m k : ℕ) : n + m + k = n + (m + k)
```

Let's prove the theorem recursively. This is exactly like defining a function
recursively (termination matters! Here we are using structural recursion so
that obvious)

```lean4
theorem Nat_zero_add (n : ℕ) : 0 + n = n := by
  match n with
  | 0 =>
    apply Nat_zero_add_zero
  | n + 1 =>
    have h : 0 + n + 1 = 0 + (n + 1) := Nat.add_assoc 0 n 1
    rw [<- h] -- or use `h.symm` or use `.symm` in the proof above.
    rw [Nat_zero_add n]
```

The version for the more mathematically inclined, with an explicit induction:

```lean4
theorem Nat_zero_add' (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => apply Nat_zero_add_zero
  | succ n ih =>
    have h : 0 + n + 1 = 0 + (n + 1) := Nat.add_assoc 0 n 1
    rw [<- h] -- or use `h.symm` or use `.symm` in the proof above.
    rw [ih]
```

Let's prove associativity of the addition now.

```lean4
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
```

(Lawful) Monads
--------------------------------------------------------------------------------

```lean4
#print Monad
-- class Monad.{u, v} (m : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- ...
--   [...].pure : {α : Type u} → α → m α
--   [...].bind : {α β : Type u} → m α → (α → m β) → m β
-- ...
```

Instead of relying only on `pure` and `bind`, the `LawfulMonad` type class in
Lean actually requires a `id_map` property of `Functor.map` (operator `<$>`)
and the proof that defines `<$>` in terms of `pure` and `bind`, which makes
the `id_map` property equivalent to the classic `bind_pure`.

```lean4
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
```

So what really matters for us in lawful monads are `pure_bind`, `bind_pure`
and `bind_assoc`.

The `Bind.kleisliRight` function is associate to the "fish" `>=>` operator.

```lean4
#print Bind.kleisliRight
-- def Bind.kleisliRight.{u, u_1, u_2} : {α : Type u} →
--  {m : Type u_1 → Type u_2} → {β γ : Type u_1} → [Bind m] → (α → m β) → (β → m γ) → α → m γ :=
-- fun {α} {m} {β γ} [Bind m] f₁ f₂ a => f₁ a >>= f₂
```

Let's prove alternate versions of the main monadic laws, based on the fish
operator and pure instead of bind and pure.

```lean4
namespace Kleisli

theorem comp_pure {α β m} [Monad m] [LawfulMonad m]
    (f : α → m β) : f >=> pure = f := by
  ext a
  rw [Bind.kleisliRight]
  apply bind_pure

theorem pure_comp {α β m} [Monad m] [LawfulMonad m]
    (f : α → m β) : pure >=> f = f := by
  ext a
  rw [Bind.kleisliRight]
  apply LawfulMonad.pure_bind

theorem comp_assoc {α β γ δ m} [Monad m] [LawfulMonad m]
    (f : α → m β) (g : β → m γ) (h : γ → m δ) :
    f >=> g >=> h = (f >=> g) >=> h := by
  ext a
  simp only [Bind.kleisliRight]
  simp only [LawfulMonad.bind_assoc]
  have h : g >=> h = fun x => g x >>= h := by
    ext a
    simp only [Bind.kleisliRight]
  simp only [h]

end Kleisli
```

Equivalence and Bijections.
--------------------------------------------------------------------------------

`Equiv α β` is a type class that establishes the existence of a bijection
between the types `α` and `β`. It is also denoted `α ≃ β`.

```lean4
#print Equiv
-- structure Equiv.{u_1, u_2} (α : Sort u_1) (β : Sort u_2) : Sort (max (max 1 u_1) u_2)
-- number of parameters: 2
-- fields:
--   Equiv.toFun : α → β
--   Equiv.invFun : β → α
--   Equiv.left_inv : Function.LeftInverse self.invFun self.toFun := by ...
--   Equiv.right_inv : Function.RightInverse self.invFun self.toFun := by ...
-- ...

#print Function.LeftInverse
-- @[implicit_reducible] def Function.LeftInverse.{u_1, u_2} : {α : Sort u_1} →
--   {β : Sort u_2} → (β → α) → (α → β) → Prop :=
-- fun {α} {β} g f => ∀ (x : α), g (f x) = x

#print Function.RightInverse
-- @[implicit_reducible] def Function.RightInverse.{u_1, u_2} : {α : Sort u_1} →
--   {β : Sort u_2} → (β → α) → (α → β) → Prop :=
-- fun {α} {β} g f => Function.LeftInverse f g
```

Note that `left_inv` and `right_inv` have default implementations. That means
that in some cases, we the default proof strategy applies, you won't have
to prove explicitly that `toFun` and `invFun` are inverses of each other.

Not also that `α ≃ β` is defined as a type, not a proposition (when either
`α` or `β` are types). The associated proposition is `Nonempty (α ≃ β)`.

```lean4
#print Nonempty
-- inductive Nonempty.{u} : Sort u → Prop
-- number of parameters: 1
-- constructors:
-- Nonempty.intro : ∀ {α : Sort u} (val : α), Nonempty α
```

Given the constructor, it's very easy to prove the proposition `Nonempty α`
when you have a term of type `α`. For example:

```lean4
example : Nonempty ℕ := Nonempty.intro 0
```

Let's prove the reflexivity, symmetry and transitivity of this equivalence.

```lean4
theorem Equiv_refl {α} : Nonempty (α ≃ α) := by
  -- Yay, here the default proof for `left_inv` and `right_inv` work!
  let equiv : α ≃ α := { toFun := id, invFun := id }
  exact Nonempty.intro equiv

theorem Equiv_symm {α β} : Nonempty (α ≃ β) → Nonempty (β ≃ α) := by
  intro nonempty
  let ⟨{toFun, invFun, left_inv, right_inv}⟩ := nonempty
  let equivInv : β ≃ α := {
    toFun := invFun,
    invFun := toFun,
    left_inv := right_inv,
    right_inv := left_inv
  }
  exact Nonempty.intro equivInv

theorem Equiv_trans {α β γ} :
    Nonempty (α ≃ β) → Nonempty (β ≃ γ) → Nonempty (α ≃ γ) := by
  intro nonempty_1  nonempty_2
  let ⟨equiv1⟩ := nonempty_1
  let ⟨equiv2⟩ := nonempty_2
  let toFun := equiv2.toFun ∘ equiv1.toFun
  let invFun := equiv1.invFun ∘ equiv2.invFun

  have left_inv : Function.LeftInverse invFun toFun := by
    rw [Function.LeftInverse]
    simp only [toFun, invFun]
    simp only [Function.comp]
    intro x
    have (b : β) : equiv2.invFun (equiv2.toFun b) = b := by
      apply equiv2.left_inv
    simp only [this]
    apply equiv1.left_inv

  have right_inv : Function.RightInverse invFun toFun := by
    simp_rw [
        Function.RightInverse, Function.LeftInverse,
        toFun, invFun,
        Function.comp
    ]
    intro x
    have (b : β) : equiv1.toFun (equiv1.invFun b) = b := by
      apply equiv1.right_inv
    simp only [this]
    apply equiv2.right_inv

  -- The compact variant of the structure notation is fancy :)
  let equiv3 : α ≃ γ := {
    toFun     -- := toFun,
    invFun    -- := invFun,
    left_inv  -- := left_inv,
    right_inv -- := right_inv,
  }

  exact Nonempty.intro equiv3
```

Now Mathlib uses this equivalent relation to build the corresponding quotient
space. The elements of this space are called cardinals. Two types `α` and
`β` have the same cardinal, denoted `#α = #β` if (and only if)
`Nonempty (α × β)` holds.


```lean4
#print Cardinal
-- def Cardinal.{u} : Type (u + 1) :=
-- Quotient Cardinal.isEquivalent

#print Cardinal.isEquivalent
-- @[instance_reducible] def Cardinal.isEquivalent.{u} : Setoid (Type u) :=
-- { r := fun α β => Nonempty (α ≃ β), iseqv := Cardinal.isEquivalent._proof_1 }


#check Cardinal.eq.mpr
-- Cardinal.eq.mpr : Nonempty (?m.1 ≃ ?m.2) → Cardinal.mk ?m.1 = Cardinal.mk ?m.2
```

Note: we need to open scoped to get the `#` notation working.

```lean4
open scoped Cardinal
```

Note how the `Even` proposition only requires that the type supports
addition! That's nifty :)

```lean4
#print Even
-- def Even.{u_2} : {α : Type u_2} → [Add α] → α → Prop :=
-- fun {α} [Add α] a => ∃ r, a = r + r
```

We're going to use `{ n : ℕ // Even n }` which is a subtype of `ℕ`.
A subtype is a structure that bundles a data `val` with an associated
proposition `property`. Here the subtype refers to the natural numbers
that are even.

```lean4
#print Subtype
-- structure Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
-- number of parameters: 2
-- fields:
--   Subtype.val : α
--   Subtype.property : p ↑self
-- constructor:
--   Subtype.mk.{u} {α : Sort u} {p : α → Prop} (val : α) (property : p val) : Subtype p

example : #ℕ = #{ n : ℕ // Even n } := by
  apply Cardinal.eq.mpr
  apply Nonempty.intro -- ⊢ ℕ ≃ { n // Even n }
  let toFun (n : ℕ) : { m : ℕ // Even m } := {
    val := 2 * n,
    property := ⟨n, show 2 * n = n + n from by grind⟩
  }
  let invFun (m : { m : ℕ // Even m }) : ℕ := (↑m : ℕ) / 2
  let left_inv : Function.LeftInverse invFun toFun := by
    simp_rw [Function.LeftInverse, toFun, invFun]
    intro x
    apply mul_div_cancel_left₀
    positivity
  let right_inv : Function.RightInverse invFun toFun := by
    simp_rw [Function.RightInverse, Function.LeftInverse, toFun, invFun]
    intro x -- ⊢ ↑⟨2 * (↑x / 2), ⋯⟩ = ↑x
    have ⟨n, hn⟩ := x.property
    apply Subtype.ext -- only the values matter
    simp only -- ⊢ 2 * (↑x / 2) = ↑x
    simp_rw [hn]
    have : n + n = 2 * n := by grind
    rw [this]
    have : (2 * n / 2) = n := by
      apply  mul_div_cancel_left₀
      positivity
    simp_rw [this]
  exact { toFun, invFun, left_inv, right_inv }
```
