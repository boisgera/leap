import Mathlib

/-!
To make sense of the finite sum `∑ i, f i`, we need

- a index type `ι` where the indices `i` live. We can actually be more
  explicit in the sum notation using `∑ i : ι, f i` if that helps.
  The index type should be finite: an instance of `Fintype ι` should exist.

- a value type `M` and function `f : ι → M`.
  Since you have no concept on order on `ι` despite that
  need to be able define the sum uniquely, you need at the very least
  associativity and commutativity to reorder the sum arbitrarily,
  and then a zero to work for an empty type.
  Technically, that requires an instance of `AddCommMonoid M`.
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
to be a commutative monoid, a simpler "cliping" behavior wouldn't work.
-/


/-!
Now, the thing is there is no `Fintype.sum`. `∑ i, f i` actually is a shortcut
for `∑ i ∈ Finset.univ, f i`, which desugars to `Finset.sum s f`, where
-/

#check Finset.sum
-- Finset.sum.{u_1, u_3} {ι : Type u_1} {M : Type u_3} [AddCommMonoid M]
-- (s : Finset ι) (f : ι → M) : M

/-!
So that expands our tooling a bit, we can now also do partial sums if we want to:
-/

#eval Finset.sum { n : Fin 10 | n <= 5 } (fun n : Fin 10 => (n : ℕ) + 1)
-- 21

/-!
which we can also write:
-/

#eval -- 21
  let f (n : Fin 10) : ℕ := (↑n : ℕ) + 1
  ∑ i ∈ { n : Fin 10 | n <= 5 }, f i

/-!
But of course, this is not limited to this case, since we can have
finite sets `Finset α` associated to non-finite types `α`.
-/

/-!
So, let's have a look at the `Finset` structure first
-/

#print Finset
-- structure Finset.{u_4} (α : Type u_4) : Type u_4
-- number of parameters: 1
-- fields:
--   Finset.val : Multiset α
--   Finset.nodup : self.val.Nodup
-- constructor:
--   Finset.mk.{u_4} {α : Type u_4} (val : Multiset α) (nodup : val.Nodup) : Finset α








#print Fintype
-- class Fintype.{u_4} (α : Type u_4) : Type u_4
-- number of parameters: 1
-- fields:
--   Fintype.elems : Finset α
--   Fintype.complete : ∀ (x : α), x ∈ Fintype.elems
-- constructor:
--   Fintype.mk.{u_4} {α : Type u_4} (elems : Finset α) (complete : ∀ (x : α), x ∈ elems) : Fintype α
