import Mathlib
set_option pp.proofs true

/-!

Basics
--------------------------------------------------------------------------------

To make sense of the finite sum `∑ i, f i`, we need

- a index type `ι`, where the indice `i` live.
  We can actually be more explicit in the sum notation in this respect,
  and use the notation `∑ i : ι, f i`.
  The index type should be finite: an instance of `Fintype ι` should exist.

- a value type `M` and function `f : ι → M`.
  Since there is no requirement that `ι` is ordered,
  to define the sum unambiguously, we need at the very least
  the associativity and commutativity of the addition.
  We also need a zero in `M` to sum over an empty type.
  To summarize, we need an instance of `AddCommMonoid M` to exist.
-/


#eval ∑ i : Fin 10, (fun (n : ℕ) => n + 1) i
-- 55

#eval 10 * (10 + 1) / 2
-- 55

/-!
Note the need to cast the index to a natural number ;
otherwise `i + 1` is computed modulo 10 (probably not what you want!).
-/

#eval ∑ i : Fin 10, (· + 1) i
-- 5

/-!
By the way, this is funny but you kinda need the wrapping behavior for `Fin 10`
for it to be a commutative monoid, a simpler "cliping" behavior wouldn't work.
-/

#synth AddCommMonoid (Fin 10)
-- Fin.addCommMonoid 10

/-!
In the same vein, `EReal` is also a commutative monoid.
(Note that ⊤ + ⊥ = ⊥ + ⊤ = ⊥. So "-∞" is at the same time "-∞" and "nan".
With this definition, when restricted to nonnegative numbers, things work
"as expected").
-/

#synth AddCommMonoid EReal
-- instAddCommMonoidEReal

/-!
Finite types to finite sets
--------------------------------------------------------------------------------

There is no `sum` function in the `Fintype` namespace.
The notation `∑ i, f i` actually is a shortcut for `∑ i ∈ Finset.univ, f i`,
which desugars to `Finset.sum s f`.
-/

#check Finset.sum
-- Finset.sum.{u_1, u_3} {ι : Type u_1} {M : Type u_3} [AddCommMonoid M]
-- (s : Finset ι) (f : ι → M) : M

/-!
So basically when we want to sum over a finite type, we actually sum over
an associated finite set that contains all the terms of the type.
The simplest set that works is the universal set over the finite type itself.
So to sum over ℕ, we actually sum over the universal set of `Set ℕ`.

**Note.** To define a `Fintype`, you actually need to:
- provide the set we have been discussing and
- prove that being a term of the type is equivalent to being an element of this set.
-/

#print Fintype
-- class Fintype.{u_4} (α : Type u_4) : Type u_4
-- number of parameters: 1
-- fields:
--   Fintype.elems : Finset α
--   Fintype.complete : ∀ (x : α), x ∈ Fintype.elems
-- constructor:
--   Fintype.mk.{u_4} {α : Type u_4} (elems : Finset α) (complete : ∀ (x : α), x ∈ elems) : Fintype α

/-!
So `Finset.univ` is very simple: that's `Fintype.elems`.
-/

#print Finset.univ
-- def Finset.univ.{u_1} : {α : Type u_1} → [Fintype α] → Finset α :=
-- fun {α} [Fintype α] => Fintype.elems

/-!
Sums over finite sets
--------------------------------------------------------------------------------

Sums over finite sets expand our tooling a bit, since we can now do partial sums
if we want to:
-/

#eval Finset.sum { n : Fin 10 | n <= 5 } (fun n : Fin 10 => (n : ℕ) + 1)
-- 21

/-!
which we can also write using the notation `∑ i ∈ s, f i`:
-/

#eval -- 21
  let f (n : Fin 10) : ℕ := (↑n : ℕ) + 1
  ∑ i ∈ { n : Fin 10 | n <= 5 }, f i

/-!
But we are not limited to finite sets inside a finite type!
We can have finite sets `Finset α` associated to non-finite types `α`,
for example
-/

#check Finset.Iic
-- Finset.Iic.{u_1} {α : Type u_1} [Preorder α] [LocallyFiniteOrderBot α]
-- (a : α) : Finset α

#eval -- 21
  let f (n : ℕ) : ℕ := n + 1
  ∑ i ∈ Finset.Iic 5, f i

/-!
This example is actually a bit too specific.

More generally, we can sum over a set of indices `s` when we know that
the associated subtype `{ x // x ∈ s }` is finite.
To do this, we use an explicit conversion to `Finset`:
-/

#check Set.toFinset
-- Set.toFinset.{u_1} {α : Type u_1} (s : Set α) [Fintype ↑s] : Finset α

#eval
  let f (n : ℕ) : ℕ := n + 1
  ∑ i ∈ { n : ℕ | n ≤ 5 }.toFinset, f i

/-!
TODO: study the `Finite` stuff. I think this is pretty standard def, with
equipotence to `Fin n` and so on. The test that a set can be coerce to a
finite set if it can be cast to a finite type is a bit weird, I guess that
testing for its finiteness **as a set** would be more natural?
-/

/-!

About `Finset`
--------------------------------------------------------------------------------

Let's have a look at the definition of the `Finset` type;
we actually need to pull a lot of extra definitions to get the full picture.
-/

#print Finset
-- structure Finset.{u_4} (α : Type u_4) : Type u_4
-- number of parameters: 1
-- fields:
--   Finset.val : Multiset α
--   Finset.nodup : self.val.Nodup
-- constructor:
--   Finset.mk.{u_4} {α : Type u_4} (val : Multiset α) (nodup : val.Nodup) : Finset α

/-!
So, a `Finset α` is defined on top of a `Multiset α`. And `Multiset α` is the
quotient of `List α` by the equivalence relation "being equal up to a permutation".
-/

#print Multiset
-- def Multiset.{u} : Type u → Type u :=
-- fun α => Quotient (List.isSetoid α)

#print List.isSetoid
-- @[instance_reducible] def List.isSetoid.{u_1} : (α : Type u_1) → Setoid (List α) :=
-- fun α => { r := List.Perm, iseqv := List.Perm.eqv α }

#print List.Perm
-- inductive List.Perm.{u} : {α : Type u} → List α → List α → Prop
-- number of parameters: 1
-- constructors:
-- List.Perm.nil : ∀ {α : Type u}, [].Perm []
-- List.Perm.cons : ∀ {α : Type u} (x : α) {l₁ l₂ : List α}, l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)
-- List.Perm.swap : ∀ {α : Type u} (x y : α) (l : List α), (y :: x :: l).Perm (x :: y :: l)
-- List.Perm.trans : ∀ {α : Type u} {l₁ l₂ l₃ : List α}, l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃

/-!
The fancy term `Setoid` means only: a base type and an associated equivalence relation.
-/

#print Setoid
-- class Setoid.{u} (α : Sort u) : Sort (max 1 u)
-- number of parameters: 1
-- fields:
--   Setoid.r : α → α → Prop
--   Setoid.iseqv : Equivalence ⇑self
-- constructor:
--   Setoid.mk.{u} {α : Sort u} (r : α → α → Prop) (iseqv : Equivalence r) : Setoid α

/-!
Ah, and a `Finset` also needs to know to prove that all elements in its
multiset are different. The definition of this is actually delegated to
the same test for the underlying lists.
-/

#print Multiset.Nodup
-- def Multiset.Nodup.{u_1} : {α : Type u_1} → Multiset α → Prop :=
-- fun {α} s => Quot.liftOn s List.Nodup Multiset.Nodup._proof_1

#print List.Nodup
-- def List.Nodup.{u} : {α : Type u} → List α → Prop :=
-- fun {α} => List.Pairwise fun x1 x2 => x1 ≠ x2


/-!
Implementation of `Finset.sum`
--------------------------------------------------------------------------------
-/

/-!
The implementation of the sum over a finite set delegates the sum to the
underlying multiset, which delegates himself to a corresponding list.
-/

#print Finset.sum
-- protected def Finset.sum.{u_1, u_3} : {ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M :=
-- fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum

#print Multiset.map
-- def Multiset.map.{v, u_1} : {α : Type u_1} → {β : Type v} → (α → β) → Multiset α → Multiset β :=
-- fun {α} {β} f s => Quot.liftOn s (fun l => ↑(List.map f l)) ⋯

#print List.sum
-- def List.sum.{u_1} : {α : Type u_1} → [Add α] → [Zero α] → List α → α :=
-- fun {α} [Add α] [Zero α] => List.foldr (fun x1 x2 => x1 + x2) 0

/-!
... but at the end of the day this is quite a mess so we need a small set
of operational theorem (split the sum, sum over empty, singleton, etc.)
to be able to make it work.
-/

/-!
Operational properties of finite sums
--------------------------------------------------------------------------------

Source: [Entries in Lean/Mathlib doc which start with `Finset.sum_`](https://leanprover-community.github.io/mathlib4_docs/search.html?q=Finset.sum_)

-/

/-!
Selection of basic results about finite sums (to be extended!):
-/

#check Finset.sum_of_isEmpty
-- Finset.sum_of_isEmpty.{u_1, u_3} {ι : Type u_1} {M : Type u_3} {f : ι → M} [AddCommMonoid M] [IsEmpty ι]
--   (s : Finset ι) : ∑ i ∈ s, f i = 0

#print IsEmpty
-- class IsEmpty.{u} (α : Sort u) : Prop
-- number of parameters: 1
-- fields:
--   IsEmpty.false : ∀ (a : α), False
-- constructor:
--   IsEmpty.mk.{u} {α : Sort u} (false : ∀ (a : α), False) : IsEmpty α

#check Finset.sum_singleton
-- Finset.sum_singleton.{u_1, u_4} {ι : Type u_1} {M : Type u_4} [AddCommMonoid M] (f : ι → M) (a : ι) :
--   ∑ x ∈ {a}, f x = f a

#check Finset.sum_union
-- Finset.sum_union.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [AddCommMonoid M] {f : ι → M}
--   [DecidableEq ι] (h : Disjoint s₁ s₂) : ∑ x ∈ s₁ ∪ s₂, f x = ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x

#check Finset.sum_add_distrib
-- Finset.sum_add_distrib.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s : Finset ι} [AddCommMonoid M] {f g : ι → M} :
--   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x

#check Finset.sum_smul
-- Finset.sum_smul.{u_1, u_5, u_6} {ι : Type u_1} {R : Type u_5} {M : Type u_6} [Semiring R] [AddCommMonoid M] [Module R M]
--   {f : ι → R} {s : Finset ι} {x : M} : (∑ i ∈ s, f i) • x = ∑ i ∈ s, f i • x

#check Finset.sum_mul
-- Finset.sum_mul.{u_1, u_4} {ι : Type u_1} {R : Type u_4} [NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R)
--   (a : R) : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
