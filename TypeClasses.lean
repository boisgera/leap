
import Mathlib

/-

**TODO:**

  - deriving

  - ToString
  - Repr
  - Add, Mul, ...
  - Inhabited
  - BEq
  - "Callable"
  - ...

  - Decidable
  - Monad ...
-/

/-
`Inhabited`
--------------------------------------------------------------------------------

-/

#check (default : Int)
-- default : Int
#eval (default: Int)
-- 0

#check (default : String)
-- default : String
#eval (default : String)
-- ""

#check (default : List String)
-- default : List String
#eval (default : List String)
-- []

#check (default : Int -> Int)
-- default : Int -> Int

def defaultFun : Int -> Int := default
#eval defaultFun 42
-- 0

#check Empty
-- Empty : Type
#print Empty
-- inductive Empty : Type
-- number of parameters: 0
-- constructors:

/--
error: failed to synthesize
  Inhabited Empty

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/ #guard_msgs in
#check (default : Empty)

namespace v0

inductive Shadok.Word where
| ga
| bu
| zo
| meu

/--
error: failed to synthesize
  Inhabited Shadok.Word

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/ #guard_msgs in
#check (default : Shadok.Word)

end v0

/-
In many instances, we can ask Lean to automatically generate an instance of
`Inhabited` for us using `deriving Inhabited`:
-/

namespace v1
inductive Shadok.Word where
| ga
| bu
| zo
| meu
deriving Inhabited

#check (default : Shadok.Word)
-- default : Shadok.Word
#eval (default : Shadok.Word)
-- v1.Shadok.Word.ga

end v1

/-
You can also define your type first and then later add the instance using
`instance ... deriving Inhabited`:
-/
namespace v2
inductive Shadok.Word where
| ga
| bu
| zo
| meu

deriving instance Inhabited for Shadok.Word

#check (default : Shadok.Word)
-- default : Shadok.Word
#eval (default : Shadok.Word)
-- v1.Shadok.Word.ga

end v2

/-
If you need a finer control on what the default value is, you can
manually define the instance:
-/

namespace v3
inductive Shadok.Word where
| ga
| bu
| zo
| meu

instance : Inhabited Shadok.Word where
  default := Shadok.Word.meu

#check (default : Shadok.Word)
-- default : Shadok.Word
#eval (default : Shadok.Word)
-- v2.Shadok.Word.meu

end v3



/-
`ToString`
--------------------------------------------------------------------------------
-/

inductive ListNat where
| nil
| cons (head : Nat) (tail : ListNat)

def empty := ListNat.nil
def one_two_three := ListNat.cons 1 (ListNat.cons 2 (ListNat.cons 3 empty))


#eval toString ([] : List Nat)
-- "[]"

#eval toString [1, 2, 3]
-- "[1, 2, 3]"

/-
We have not told Lean (yet) how to represent our custom list of `Nat` as a string:
-/

/--
error: failed to synthesize
  ToString ListNat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
#guard_msgs in
#eval toString empty

/--
error: failed to synthesize
  ToString ListNat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/ #guard_msgs in
#check (inferInstance : ToString ListNat)

/-
When `#eval`'d, Lean's built-in representation is used:
-/

/--
info: ListNat.nil
-/
#guard_msgs in
#eval empty

/--
info: ListNat.cons 1 (ListNat.cons 2 (ListNat.cons 3 (ListNat.nil)))
-/
#guard_msgs in
#eval one_two_three

/-
Now let's define a custom representation of ours lists of Nats as a string.
We will define it as a method named `toString` in the `ListNat` namespace;
that is reasonable but not at all mandatory.
-/

def ListNat.toString (Nats : ListNat) : String :=
  match Nats with
  | nil => ""
  | cons n ns => (List.replicate n "·" |> "".intercalate) ++ " " ++ (ListNat.toString ns)

#eval ListNat.toString empty
-- ""

#eval ListNat.toString one_two_three
-- "· ·· ··· "

/--
Now we can use this function to register `ListNat` as an instance of the
type class `ToString ListNat`:
-/

instance : ToString ListNat where
  toString := ListNat.toString

/-
At this point, we can use the generic `toString` function of `Lean` that is
"hooked" to this type class to represent our lists of ints:
-/

#eval toString empty
-- ""

#eval toString one_two_three
-- "· ·· ··· "

/-
All mechanisms that rely on terms being instances of `ToString` now work.
For example, `#eval`:
-/

#eval empty
--

#eval one_two_three
-- · ·· ···

/-
Functions can also require instances of `ToString`:
-/

#check IO.println
-- IO.println.{u_1} {α : Type u_1} [ToString α] (s : α) : IO Unit

#eval IO.println one_two_three
-- · ·· ···

/-
Repr
--------------------------------------------------------------------------------
-/

/-
`Add`
--------------------------------------------------------------------------------
-/

/--
info: "Hello world!"
-/
#guard_msgs in
#eval "Hello" ++ " " ++ "world!"

/--
error: failed to synthesize
  HAdd String String ?m.4

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#eval "Hello" + "World!"

instance : Add String where
  add := fun s1 s2 => s1 ++ " " ++ s2

/--
info: "Hello world!"
-/
#guard_msgs in
#eval "Hello" + "world!"

#check List.sum
-- List.sum.{u_1} {α : Type u_1} [Add α] [Zero α] : List α → α

#eval List.sum [1, 2, 3]
-- 6

#check (inferInstance : Add Nat)
-- inferInstance : Add Nat
#check (inferInstance : Zero Nat)
-- inferInstance : Zero Nat
#synth Add Nat
-- instAddNat
#check instAddNat
-- instAddNat : Add Nat
#print instAddNat
-- def instAddNat : Add Nat :=
-- { add := Nat.add }


instance : Zero String where
  zero := ""

#eval List.sum ["It", "is", "what", "it", "is"]
-- "It is what it is "

/-
`BEq`
--------------------------------------------------------------------------------
-/

/-
`DecidableEq`
--------------------------------------------------------------------------------
-/


/-
Example
--------------------------------------------------------------------------------
-/

/--
TODO: get rid of the `denom_ne_0` if you don't like/understand it!
-/

structure Q where
  num : Int := 0
  denom : Int := 1
  denom_ne_0 : denom ≠ 0 := by decide -- or BYOP!

#eval Q.mk 1 2
-- { num := 1, denom := 2, denom_ne_0 := _ }

/--
error: could not synthesize default value for parameter 'denom_ne_0' using tactics
---
error: Tactic `decide` proved that the proposition
  0 ≠ 0
is false
-/
#guard_msgs in
#eval Q.mk 1 0

instance : Inhabited Q where
  default := Q.mk 0 1 (by decide)

#eval (default : Q)
-- { num := 0, denom := 1, denom_ne_0 := _ }

def Q.toString (q : Q) : String :=
  (ToString.toString q.num) ++ " / " ++ (ToString.toString q.denom)

instance : ToString Q where
  toString := Q.toString

#eval (default : Q)
-- 0 / 1

#check mul_ne_zero
-- ∀ {M₀ : Type u_1} [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀} (ha : a ≠ 0) (hb : b ≠ 0), a * b ≠ 0

def Q.add (q r : Q) : Q :=
  {
    num := q.num * r.denom + r.num * q.denom,
    denom := q.denom * r.denom,
    denom_ne_0 := mul_ne_zero q.denom_ne_0 r.denom_ne_0
  }

instance : Add Q where
  add := Q.add

#eval Q.mk 1 2 + Q.mk 1 3
-- 5 / 6

def Q.beq (q r : Q) : Bool :=
  (q.num * r.denom) == (r.num * q.denom)

instance : BEq Q where -- not lawful 😢
  beq := Q.beq

#eval Q.mk 1 2 == Q.mk 2 4
-- true

#eval Q.mk 1 2 == Q.mk 1 3
-- false
