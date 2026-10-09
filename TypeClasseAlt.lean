
namespace Bubble

inductive Bool : Type where
  | false : Bool
  | true : Bool

/-!
We can't directly print a term of type `Bool`, which kinda makes sense (Lean doesn't know how we want to represent `false` and `true` as strings of text)
-/

#eval IO.println Bool.false
-- failed to synthesize instance of type class
--   ToString Bool

/-!
So we provide a function to perform that conversion
-/
def Bool.toString : Bool → String
  | false => "false"
  | true => "true"

/-!
and we use it.
-/

#eval IO.println (Bool.toString Bool.false)
-- false

/-!
That works, but it is a bit heavy. In constrast, terms of built-in types like `Nat` don't have to do that:
-/

#eval IO.println 42
-- 42

/-!
and indeed, `IO.println` doesn't merely accept `String` terms: it accepts terms of any
type `α` for which Lean can infer (implictly) the existence of a instance of `ToString α`.
-/

#check IO.println
-- IO.println.{u_1} {α : Type u_1} [ToString α] (s : α) : IO Unit


/-!
`ToString` is a type class. It is very similar to a structure, but its definition
uses the keyword `class` instead of `structure`
-/

#print ToString
-- class ToString.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   ToString.toString : α → String
-- constructor:
--   ToString.mk.{u} {α : Type u} (toString : α → String) : ToString α

/-!
Let's define an instance of `ToString Bool`. We only have a single field to provide,
`toString`, which is a function `Bool → String` and we have already defined this
function: that's `Bool.toString`.
Terms of this type (instances of the type class) are meant to be implicitly
inferred instead of being explicitly provided.
-/

instance : ToString Bool := {
  toString := Bool.toString
}

/-!
Now we can let Lean infer automatically what the instance of `ToString Bool` is when
we print a Bool:
-/

#eval IO.println Bool.false
-- false

/-!
To understand what's going on, it's worth noting that we can be explicit and provide
the instance ourselves if we want (although that's rarelay need). When we have defined
the instance, we haven't given a name thus Lean has named the instance `instToStringBool` by default. We can actually select another name if we want:
-/


instance instToStringBool' : ToString Bool := {
  toString := Bool.toString
}

/-!
and then use this instance in a version of `IO.println` where every argument has been
made explicit:
-/

#check @IO.println
-- @IO.println : {α : Type u_1} → [ToString α] → α → IO Unit

#eval @IO.println Bool instToStringBool' Bool.false
-- false




end Bubble
