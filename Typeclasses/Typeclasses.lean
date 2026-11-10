
/-! Terminology : typeclasses vs traits/interfaces

Roughly speacking: we want some "operations" to be generic (apply to different
types, including some that are not created yet when the function is written),
but not *every* type. The types have to have some properties.
-/

/-! The problem and how part of it can be solved without typeclasses:
carrying extra argument structures that give the required (external)
info.
-/

#check Bool

namespace Sandbox

/-!
TODO: `Point` with `Add` is a better example afaict.
-/

inductive Bool where
| false : Bool
| true : Bool

#eval Bool.false
-- Sandbox.Bool.false

-- generic multiply-add
def mulAdd {α} (add : α → α → α) (mul : α → α → α) (a b c : α) : α :=
  add (mul a b) c

def Bool.add(a b : Bool) : Bool :=
  match a, b with
  | false, false => false
  | false, true  => true
  | true , false => true
  | true , true  => true

def Bool.mul(a b : Bool) : Bool :=
  match a, b with
  | false, _     => false
  | _    , false => false
  | true , true  => true

#eval mulAdd Bool.add Bool.mul Bool.true Bool.true Bool.true
-- Sandbox.Bool.true

/-!
This is heavy! We have to carry `Bool.add` and `Bool.mul` along for each
operation, despite the fact that they are always the same...
We could make thing a bit easier by "bundling" them is a given
structure, but at the very least we have to carry one explicit argument
along for each operation that expects type with "+".

We'd like to declare the support of `Bool` for addition and multiplication
once and for all, register our implementation and never pass our implementation
as an argument ever again.
-/

#eval "jkdjsjds" ++ "----" ++ "kdjskdsjkd"

/-!

The signature of `Add` and `Mul`. Very similar to a structure, with `class`
instead of `structure`.

```lean
class Add (α : Type u) where
  add : α → α → α
```

```lean
class Mul (α : Type u) where
  mul : α → α → α
```
-/

def mulAdd' {α} [instAdd : Add α] [instMul : Mul α] (a b c : α) : α :=
  instAdd.add (instMul.mul a b) c

/-!
Let's declare `Add` and `Mul` instances for our type.
-/

instance : Add Bool where
  add := Bool.add

instance : Mul Bool where
  mul := Bool.mul

/-!
Now we can use
-/

#eval mulAdd' Bool.true Bool.true Bool.true
-- Sandbox.Bool.true

/-!
Now luckily for us, Lean 4 has "hooked" the `+` and `*` symbols to the
corresponding methods of the `Add` and `Mul` typeclasses. This is a
very common scheme and that allow use to have an even leaner implementation
of `mulAdd`:
-/

def mulAdd'' {α} [Add α] [Mul α] (a b c : α) : α :=
  a * b + c

#eval mulAdd'' Bool.true Bool.true Bool.true
-- Sandbox.Bool.true

/-!
Now, since the notation `+` is not hardcoded but associated to a typeclass,
we can reuse it (automatically) for new types, or old types for which we
want to extend the functionalities.
-/

instance : Add String where
  add := fun (s t : String) => s ++ " " ++ t

#eval "Hello" + "world!"
-- "Hello world!"

end Sandbox



/-!
Useful typeclasses
-/

structure Point where
  x : Float
  y : Float

#eval Point.mk 0.0 1.0
-- { x := 0.000000, y := 1.000000 }

/-!
The `toString` method comes from the `ToString` typeclass:
-/

#check toString
-- ToString.toString.{u} {α : Type u} [self : ToString α] : α → String

#print ToString
-- class ToString.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   ToString.toString : α → String
-- constructor:
--   ToString.mk.{u} {α : Type u} (toString : α → String) : ToString α

/-!
The `Float` type has an instance of this typeclass, that we can find with:

  - The online doc,
  - `#synth` or
  - `inferInstance`.

-/

#synth ToString Float
-- instToStringFloat

#check instToStringFloat
-- instToStringFloat : ToString Float

@[reducible]
def instToStringFloat' : ToString Float := inferInstance


-- Human consumption
instance : ToString Point where
  toString (p : Point) := "(" ++ (toString p.x) ++ ", " ++ (toString p.y) ++ ")"

#eval Point.mk 0.0 1.0
-- (0.000000, 1.000000)

/-!

> The `Repr` type class is used to provide a standard representation for data
> that can be parsed and evaluated to obtain an equivalent value.

-/

#print Repr
-- class Repr.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   Repr.reprPrec : α → Nat → Std.Format
-- constructor:
--   Repr.mk.{u} {α : Type u} (reprPrec : α → Nat → Std.Format) : Repr α

#print Std.Format
-- inductive Std.Format : Type
-- number of parameters: 0
-- constructors:
-- Std.Format.nil : Std.Format
-- Std.Format.line : Std.Format
-- Std.Format.align : Bool → Std.Format
-- Std.Format.text : String → Std.Format
-- Std.Format.nest : Int → Std.Format → Std.Format
-- Std.Format.append : Std.Format → Std.Format → Std.Format
-- Std.Format.group : Std.Format → optParam Std.Format.FlattenBehavior Std.Format.FlattenBehavior.allOrNone → Std.Format
-- Std.Format.tag : Nat → Std.Format → Std.Format

#eval max_prec
-- 1024

#check repr
-- repr.{u_1} {α : Type u_1} [Repr α] (a : α) : Std.Format

instance : Repr Point where
  reprPrec (p : Point) (prec : Nat) :=
  dbg_trace ("*** prec: " ++ toString prec)
  if prec ≥ max_prec then
    -- Function application bind the tightest
    -- so we only have to worry in this case
    Std.Format.text (
      "(Point.mk " ++
      toString p.x ++
      " " ++
      toString p.y ++
      ")"
    )
  else
    Std.Format.text (
      "Point.mk " ++
      toString p.x ++
      " " ++
      toString p.y
    )


#eval Point.mk 0.0 1.0 -- no paren needed: here in this context, prec = 0
-- *** prec: 0
-- Point.mk 0.000000 1.000000

def listOfPoints := [Point.mk 0.0 0.0, Point.mk 0.0 1.0, Point.mk 1.0 1.0]

#eval listOfPoints
-- *** prec: 0
-- *** prec: 0
-- *** prec: 0
-- [Point.mk 0.000000 0.000000, Point.mk 0.000000 1.000000, Point.mk 1.000000 1.000000]

#eval some (Point.mk 0.0 1.0) -- here the paren are needed!
-- *** prec: 1024
-- some (Point.mk 0.000000 1.000000)

/-!
`Repr` can also specify breakpoints, etc that are very helpful
to help Lean format appropriately long representations.
-/

#eval Std.Format.pretty (repr (Point.mk 0.0 1.0)) (width := 10)


structure Point' where
  x : Float
  y : Float

instance : Repr Point' where
  reprPrec (p : Point') (_ : Nat) :=
    Std.Format.group ( -- group is necessary to avoid hard line breaks.
      Std.Format.text "(Point.mk" ++ Std.Format.line ++
      repr p.x ++ Std.Format.line ++
      repr p.y ++ Std.Format.line ++
      Std.Format.text ")"
    )

#eval Std.Format.pretty (repr (Point'.mk 0.0 1.0))
-- "(Point.mk 0.000000 1.000000)"

#eval Std.Format.pretty (repr (Point'.mk 0.0 1.0)) (width := 10)
-- "(Point.mk\n0.000000\n1.000000\n)"

/-! Automatically deriving typeclasses instances: `deriving`
-/

/-!
TODO:
"Useful"
1. Monad (and its hierarchy: Functor, Applicative)
The backbone of do-notation, Option, Except, StateM, IO, elaboration monads (MetaM, TacticM), everything. Understanding bind/pure and how Applicative sits underneath is essential – and since you've been working through StateM/OptionT, you've already seen how monad transformers stack on this hierarchy via MonadLift.
2. DecidableEq / Decidable
Underpins if-then-else inside proofs, pattern matching on propositions, and is what lets decide close goals. Every time you write if h : p then ... else ... you're relying on Decidable p. It's also the bridge between computational content and propositional content – a nice thing to foreground pedagogically since it's where students first feel Prop vs. Bool tension.
3. Coe (and friends: CoeSort, CoeFun, CoeHead/CoeTail)
You've spent real time on CoeFun already. The whole coercion family is what makes Nat → Int silent, lets structures be used as their carrier type (CoeSort), and lets bundled objects like MonoidHom be applied like functions (CoeFun). It's also a frequent source of "why did elaboration do that?!" confusion, so it's worth knowing cold.
4. Ord / LT / LE (the ordering hierarchy)
Less glamorous, but shows up everywhere: compare, <, ≤, and their interaction with Decidable (decLt, etc.) and with LinearOrder in Mathlib. Good one to include if your course touches sorting algorithms, omega, or numeric proofs.
5. Repr / ToString / BEq

TODO: Python-like

Add, Sub, Mul, Div, Mod, Neg, HPow
BEq, DecidableEq
LT, LE
Hashable
GetElem, GetElem?
Membership
ForIn, ForM
CoeFun
Coe, CoeSort, CoeHead
Repr
ToString
Decidable

TODO: simplest

Inhabited
Add
Mul
Neg
BEq
ToString
Repr
Append
Membership
Coe

-/


#eval 1 ∈ [0, 1, 2, 3]
-- true

/-!

Inhabited Types
--------------------------------------------------------------------------------

Types that declare a default value:

-/

#print Inhabited
-- class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
-- number of parameters: 1
-- fields:
--   Inhabited.default : α
-- constructor:
--   Inhabited.mk.{u} {α : Sort u} (default : α) : Inhabited α


#check default
-- Inhabited.default.{u} {α : Sort u} [self : Inhabited α] : α

#eval (default : Nat)
-- 0

#eval (default : String)
-- ""

inductive Rhyme : Type where
| enny : Rhyme
| meeny : Rhyme
| miny : Rhyme
| moe : Rhyme

instance : Inhabited Rhyme where
  default := Rhyme.moe

#eval (default : Rhyme)
-- Rhyme.moe

inductive MyNat : Type where
| zero : MyNat
| succ (n : MyNat) : MyNat
deriving Inhabited -- picks the first non-recursive constuctor with Inhabited arguments

#eval (default : MyNat)
-- MyNat.zero

/-!
`BEq`, `DecidableEq` and `Hashable`
--------------------------------------------------------------------------------

`BEq` is the type class associated to the boolean-valued equality relation.

-/

#print BEq
-- class BEq.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   BEq.beq : α → α → Bool
-- constructor:
--   BEq.mk.{u} {α : Type u} (beq : α → α → Bool) : BEq α

#check BEq.beq
-- BEq.beq.{u} {α : Type u} [self : BEq α] : α → α → Bool

/-!
The associated operator notation is `==`:
-/

#synth BEq Nat
-- instBEqOfDecidableEq

#check instBEqOfDecidableEq
-- instBEqOfDecidableEq.{u_1} {α : Type u_1} [DecidableEq α] : BEq α

#eval instBEqOfDecidableEq.beq 0 1
-- false

#eval 0 == 1
-- false

/-!
Note that in this case, the instance of `BEq` was not implemented directly
but derived from the fact that natural numbers instantiate `DecidableEq`.
Their propositional equality is decidable: it can be algorithmically checked
and converted to a boolean.
-/

#print DecidableEq
-- @[reducible] def DecidableEq.{u} : Sort u → Sort (max 1 u) :=
-- fun α => (a b : α) → Decidable (a = b)

#print Decidable
-- inductive Decidable : Prop → Type
-- number of parameters: 1
-- constructors:
-- Decidable.isFalse : {p : Prop} → ¬p → Decidable p
-- Decidable.isTrue : {p : Prop} → p → Decidable p

#check decide
-- Decidable.decide (p : Prop) [h : Decidable p] : Bool

/-!

TODO: `LawfulBEq`

-/

/-!

As a consequence
-/

#check (0 = 1 : Prop)
-- 0 = 1 : Prop

#check (0 = 1 : Bool)
-- decide (0 = 1) : Bool

/-!

`Hashable` instances

Similar to what you get in Python to use in sets or as keys in dict.


-/

#print Hashable
-- class Hashable.{u} (α : Sort u) : Sort (max 1 u)
-- number of parameters: 1
-- fields:
--   Hashable.hash : α → UInt64
-- constructor:
--   Hashable.mk.{u} {α : Sort u} (hash : α → UInt64) : Hashable α

#check (inferInstance : Hashable String)

#eval hash "Hello world!"
-- 16151149566053711823

#print LawfulHashable
-- class LawfulHashable.{u} (α : Type u) [BEq α] [Hashable α] : Prop
-- number of parameters: 3
-- fields:
--   LawfulHashable.hash_eq : ∀ (a b : α), (a == b) = true → hash a = hash b
-- constructor:
--   LawfulHashable.mk.{u} {α : Type u} [BEq α] [Hashable α] (hash_eq : ∀ (a b : α), (a == b) = true → hash a = hash b) :
--     LawfulHashable α

/-!
TODO: LT, LE, Ord
-/

#print LT
-- class LT.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   LT.lt : α → α → Prop
-- constructor:
--   LT.mk.{u} {α : Type u} (lt : α → α → Prop) : LT α

#print LE
-- class LE.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   LE.le : α → α → Prop
-- constructor:
--   LE.mk.{u} {α : Type u} (le : α → α → Prop) : LE α

#print Ord
-- class Ord.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   Ord.compare : α → α → Ordering
-- constructor:
--   Ord.mk.{u} {α : Type u} (compare : α → α → Ordering) : Ord α

#print Ordering
-- inductive Ordering : Type
-- number of parameters: 0
-- constructors:
-- Ordering.lt : Ordering
-- Ordering.eq : Ordering
-- Ordering.gt : Ordering

/-!
HashTable Example (without resizing)
--------------------------------------------------------------------------------
-/


structure HashTable (α β) [BEq α] [Hashable α] where
  buckets : Array (List (α × β))

def HashTable.new (α β) [BEq α] [Hashable α] : HashTable α β :=
  Array.replicate 8 [] |> HashTable.mk

def HashTable.get {α β} [BEq α] [Hashable α] (h : HashTable α β) (k : α) : Option β :=
  let hi := hash k % 8 |>.toNat
  let bucket := (h.buckets)[hi]!
  let kv? := bucket.find? (fun (kv) => (kv.1 == k))
  match kv? with
  | none => none
  | some kv => kv.2

def HashTable.set {α β} [BEq α] [Hashable α] (h : HashTable α β) (k : α) (v : β) :
    HashTable α β :=
  let hi := hash k % 8 |>.toNat
  let bucket := (h.buckets)[hi]!
  let i? := bucket.findIdx? (fun (kv) => (kv.1 == k))
  let bucket := match i? with
  | none => ((k, v) :: bucket)
  | some i => bucket.set i (k, v)
  bucket |> h.buckets.set! hi |> HashTable.mk

instance {α β} [BEq α] [Hashable α] [ToString α] [ToString β] :
    ToString (HashTable α β) where
  toString (h : HashTable α β) :=
    let parts := h.buckets.map (fun (item) => toString item) |>.toList
    String.intercalate "\n" parts


def makeHT (n : Nat) : HashTable String String :=
  let ht_empty := HashTable.new String String
  let kvs := (List.range n).map (fun i => (s!"key_{i}", s!"val_{i}"))
  List.foldl
    (fun (ht : HashTable String String) (kv : String × String) =>
        ht.set kv.1 kv.2
    )
    (init := ht_empty)
    kvs

#eval makeHT 10
-- [(key_3, val_3)]
-- []
-- [(key_8, val_8), (key_7, val_7)]
-- [(key_4, val_4), (key_2, val_2)]
-- [(key_0, val_0)]
-- [(key_1, val_1)]
-- [(key_6, val_6), (key_5, val_5)]
-- [(key_9, val_9)]

#eval (makeHT 10).get "key_0"
-- some "val_0"

#eval (makeHT 10).get "key_99"
-- none

#eval (makeHT 10).get "key_6"
-- some "val_6"

#eval (makeHT 10).get "key_5"
-- some "val_5"

#eval makeHT 10 |>.set "key_10" "val_10"
-- [(key_3, val_3)]
-- [(key_10, val_10)]
-- [(key_8, val_8), (key_7, val_7)]
-- [(key_4, val_4), (key_2, val_2)]
-- [(key_0, val_0)]
-- [(key_1, val_1)]
-- [(key_6, val_6), (key_5, val_5)]
-- [(key_9, val_9)]

#eval makeHT 10 |>.set "key_0" "val_99"
-- [(key_3, val_3)]
-- []
-- [(key_8, val_8), (key_7, val_7)]
-- [(key_4, val_4), (key_2, val_2)]
-- [(key_0, val_99)]
-- [(key_1, val_1)]
-- [(key_6, val_6), (key_5, val_5)]
-- [(key_9, val_9)]

#eval makeHT 10 |>.set "key_6" "val_66" |>.set "key_5" "val_55"
-- [(key_3, val_3)]
-- []
-- [(key_8, val_8), (key_7, val_7)]
-- [(key_4, val_4), (key_2, val_2)]
-- [(key_0, val_0)]
-- [(key_1, val_1)]
-- [(key_6, val_66), (key_5, val_55)]
-- [(key_9, val_9)]
