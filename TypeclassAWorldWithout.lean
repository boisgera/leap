

namespace My

-- Idea / example : make arithmetic functions that are polymorphic wrt the + and * ops.
-- (should work for Nat as well as our ZOI number)
-- TODO: add a field somehow and not merely functions? The zero? one?
-- yes, that would be nice...
-- TODO: group mul and add inside a structre before making it a class
-- TODO: add props, such as add_zero and zero_add.


inductive ZOI where
  | zero
  | one
  | inf

-- default? toBool? toString? Add, Mul?

def ZOI.add (m n : ZOI) : ZOI :=
  match m, n with
  | inf, _ => inf
  | _, inf => inf
  | zero, zero => zero
  | zero, one => one
  | one, zero => one
  | one, one => inf


def ZOI.mul (m n : ZOI) : ZOI :=
  match m, n with
  | zero, _ => zero
  | _, zero => zero
  | one, one => one
  | one, inf => inf
  | inf, one => inf
  | inf, inf => inf


def Nat.mulAdd (m n p : Nat) : Nat :=
  Nat.add (Nat.mul m n) p

def ZOI.mulAdd (m n p : ZOI) : ZOI :=
  ZOI.add (ZOI.add m n) p

-- Well, that's some duplication ... instead we could make the mulAdd operation
-- generic wrt the type. Except that 1) the type has to have support for + and *
-- 2) should bring them explicitly when mulAdd is called.

def mulAdd {α} (add : α → α → α) (mul : α → α → α) (m n p : α) : α :=
  add (mul m n) p

#eval mulAdd ZOI.add ZOI.mul ZOI.one ZOI.one ZOI.one
-- My.ZOI.inf

#eval mulAdd Nat.add Nat.mul 1 1 1
-- 2

-- This is nice, except that this is heavy. Can't we 1) register what the add
-- and mul are for Nat and ZOI once and for all 2) let Lean find automatically
-- these functions when we call the generic mulAdd? Yes we can!
-- We need to define a "structure" (type class) with the special keywork `class`
-- instead of `structure` meant to store those functions.

class Arithmetic (α : Type) where
  add : α → α → α
  mul : α → α → α

/-!
And then instantiate this typeclass for all the type we want to use it with:
-/

instance : Arithmetic Nat where
  add := Nat.add
  mul := Nat.mul

instance : Arithmetic ZOI where
  add := ZOI.add
  mul := ZOI.mul

/-!
Now we can redefine mulAdd in a generic -- but constrained -- way which is more
convenient to use:
-/

def mulAdd' {α : Type} [Arithmetic α] (m n p : α) :=
  Arithmetic.add (Arithmetic.mul m n) p

/-!
Lean will automatically ensure that α has a registered instance of Arithmetic α,
find it, and dispatch the Arithmetic field access to the appropriate instance.
-/

#eval mulAdd' ZOI.one ZOI.one ZOI.one
-- My.ZOI.inf

#eval mulAdd' 1 1 1

end My
