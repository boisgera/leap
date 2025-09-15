
/-
Product Types
--------------------------------------------------------------------------------

## Tuples

-/

def pair := (42, "hello")

#check pair
-- pair : Nat × String

#eval pair
-- (42, "hello")

#eval pair.1
-- 42

#eval pair.2
-- "hello"

#eval pair.fst
-- 42

#eval pair.snd
-- "hello"

def swap {α β} : α × β -> β × α := fun pair =>
  let (a, b) := pair
  (b, a)

#eval swap (42, "hello")
-- ("hello", 42)

#eval (fun (a, b) => (b, a)) (42, "hello")
-- ("hello", 42)


def triple := (42, "hello", true)

#eval triple
-- (42, "hello", true)

#check triple
-- triple : Nat × String × Bool

#eval triple.1
-- 42

#eval triple.2
-- ("hello", true)

#eval triple.2.1
-- "hello"

#eval triple.2.2
-- true

#check Nat × (String × Bool)
-- Nat × (String × Bool) : Type

#eval (42, ("hello", true))
-- (42, ("hello", true))

#eval (fun (a, b, c) => (b, c, a)) (42, "hello", true)
-- ("hello", true, 42)

/-
So there is not really a n-uple for n>=2, and no 1-uple or 0-uple either.
Only pairs, and nested pairs!
-/

/-
## Structures

Similar to tuples, but with named fields.


--/

structure Person where
  name : String
  age : Nat
  alive : Bool
deriving Repr

#eval Person.mk "Alice" 30 true
-- { name := "Alice", age := 30, alive := true }

#check Person.mk
-- Person.mk (name : String) (age : Nat) (alive : Bool) : Person

def alice : Person := { name := "Alice", age := 30, alive := true }

#eval alice
-- { name := "Alice", age := 30, alive := true }

#eval alice.name
-- "Alice"

#eval alice.age
-- 30

#eval alice.alive
-- true

def alice' : Person := { alice with age := 31 }

#eval alice'
-- { name := "Alice", age := 31, alive := true }

structure Person' where
  name : String
  age : Nat
  alive : Bool := true -- default value
deriving Repr

def alice'' : Person' := { name := "Alice", age := 30 }

#eval alice''
-- { name := "Alice", age := 30, alive := true }

def bob : Person' := { name := "Bob", age := 125, alive := false }

#eval bob
-- { name := "Bob", age := 125, alive := false }


/-
Sum Types
--------------------------------------------------------------------------------
-/

/-
## Disjoint Unions
--/

def left : Nat ⊕ String := Sum.inl 42

#eval left
-- Sum.inl 42

def right : Nat ⊕ String := Sum.inr "hello"

#eval right
-- Sum.inr "hello"

#check Nat ⊕ (String ⊕ Bool)
-- Nat ⊕ String ⊕ Bool : Type

def nestedRight : Nat ⊕ String ⊕ Bool := Sum.inr (Sum.inr true)
#eval nestedRight
-- Sum.inr (Sum.inr true)

#eval match nestedRight with
  | Sum.inl n => IO.println s!"It's a Nat: {n}"
  | Sum.inr (Sum.inl s) => IO.println s!"It's a String: {s}"
  | Sum.inr (Sum.inr b) => IO.println s!"It's a Bool: {b}"
-- It's a Bool: true

/-
# Enums

```python
from enum import Enum

# class syntax
class Color(Enum):
    RED = 1
    GREEN = 2
    BLUE = 3
```

POW: enums are all distincts. Abstraction over values (avoid magic numbers, we could even "auto" the numbers).

Lean lessons: exclusive and exhaustive (display pattern matching)

-/

-- There are only two kinds of languages:

inductive LanguageKind where
| theOnesPeopleComplainAbout
| theOnesNobodyUses


/-
## parametrized enums


```rust
enum Shape {
    Point,
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 }
}
```

-/


/-

## Recursive (/inductive) enums aka algebraic data types

```rust
enum List {
    Nil,
    Cons(i32, Box<List>),
}
```

-/

/-
## Algebraic data types

### What is `B`?

-/

inductive B where
  | f : B
  | t : B
deriving Repr -- for convenience

#check B
-- B : Type


/-
The new type `B` has two **constructors** `B.f` and `B.t`.
-/


#check B.f
-- B.f : B

#eval B.f
-- B.f

#check B.t
-- t : B

#eval B.t
-- B.t

/-
Since constructors have to deliver a value of type `B`,
the declaration of the type of `f` and `t` is actually optional.
-/

inductive B' where
  | f
  | t

/-
This list of constructors is exhaustive and exclusive, meaning that

  - every value of type `B` is either `B.f` or `B.t`

  - no value can be both.

-/

/-
So our `B` type is isomorphic to the `Bool` type, with `B.f`
corresponding to `false` and `B.t` to `true`.

-/

/-
Handling of inductive types is done by pattern matching.
-/

def B.not (b : B) : B :=
  match b with
  | B.f => B.t
  | B.t => B.f

#eval B.not B.f
-- B.t

#eval B.f.not
-- B.t

#eval B.not B.t
-- B.f

def B.not' : B -> B
  | B.f => B.t
  | B.t => B.f

def B.not'' : B -> B
  | f => B.t
  | t => B.f

def B.and (b1 b2 : B) : B :=
  match b1 with
  | B.f => B.f
  | B.t => match b2 with
    | B.f => B.f
    | B.t => B.t

#eval B.and B.f B.f
-- B.f

#eval B.and B.f B.t
-- B.f

#eval B.f.and B.f
-- B.f

def and' : B -> B -> B
  | B.f, _ => B.f
  | _, B.f => B.f
  | B.t, B.t => B.t

/-
### What is `O`?
-/

/-
The constructors of an inductive type can take arguments.
-/

inductive O where
  | n : O
  | s (b : B) : O
deriving Repr -- for convenience

/-
Alternatively, the terser:
-/

inductive O' where
  | n
  | s (b : B)

/-
To create values of type `O`, we use the constructors:
-/

#eval O.n
-- O.n

#eval O.s B.f
-- O.s (B.f)

#eval O.s B.t
-- O.s (B.t)

/-
This is the complete list of values of type `O` that you can create,
and they are all distinct.
-/

/-
Here `O` represents an option type: a value of type is either one
of the value of type `B` (i.e. false, true), or nothing ("undefined").

With this in mind, we could reimplement our version of `not` and `and`
for this type:
-/

def O.not (o : O) : O :=
  match o with
  | O.n => O.n
  | O.s b => O.s (B.not b)

#eval O.not O.n
-- O.n

#eval O.not (O.s B.f)
-- O.s (B.t)

#eval O.not (O.s B.t)
-- O.s (B.f)

def O.and (o1 o2 : O) : O :=
  match o1 with
  | O.n => O.n
  | O.s b1 => match o2 with
    | O.n => O.n
    | O.s b2 => O.s (B.and b1 b2)

#eval O.and O.n O.n
-- O.n

#eval O.and O.n (O.s B.f)
-- O.n

#eval O.and O.n (O.s B.t)
-- O.n

#eval O.and (O.s B.f) O.n
-- O.n

#eval O.and (O.s B.f) (O.s B.f)
-- O.s (B.f)

#eval O.and (O.s B.f) (O.s B.t)
-- O.s (B.f)

/-
### What is `N`?

Our first example which is actually recursive!
-/

inductive N where
  | z : N
  | s (n : N) : N

/-
Alternatively, the terser:
-/

inductive N' where
  | z
  | s (n : N')

/-
or the variant that makes the type of each constructor explicit:
-/

inductive N'' where
  | z : N''
  | s : N'' -> N''
deriving Repr -- for convenience

/-
What these definitions say is that a value of type `N` is either

  - the constructor `N.z`, or

  - the constructor `N.s` applied to another (pre-existing) value of type `N`.
-/

#eval N.z
-- N.z

#eval N.s N.z
-- N.s (N.z)

#eval N.s (N.s N.z)
-- N.s (N.s (N.z))

#eval N.s (N.s (N.s N.z))
-- N.s (N.s (N.s (N.z)))

#eval N.z.s.s.s
-- N.s (N.s (N.s (N.z)))

/-
### What is `L`?
-/

inductive L where
  | n : L
  | c (h : N) (t : L) : L

inductive L' where
  | n
  | c (h : N)

inductive L'' where
  | n : L''
  | c : N -> L'' -> L''

/-
### What is `T`?
-/

inductive T where
  | l (n : N) : T
  | b (l: T) (r : T) : T

inductive T' where
  | l (n : N)
  | b (l: T') (r : T')

inductive T'' where
  | l : N -> T''
  | b : T'' -> T'' -> T''


/-





-- There are only two kinds of languages:
inductive LanguageKind where
  | onePeopleComplainAbout
  | oneNobodyUses


inductive N where
  | z : N
  | s (n : N) : N -- or s : N -> N
deriving Repr -- Ah, funny, ToString is derived by default, not Repr
-- and this is required for the recursive representation to work AFAICT.

#eval N.z

#eval N.s N.z

#eval N.s (N.s N.z)

inductive L where
  | n : L
  | c (h : N) (t : L) : L -- or c : N -> L -> L

#eval L.n

#eval L.c (N.z) (L.n)

#eval L.c (N.s N.z) (L.c (N.z) (L.n))

inductive T where
  | l (n : N) : T
  | b (l: T) (r : T) : T -- or b : T -> T -> T

#eval T.l (N.z)

#eval T.b (T.l (N.z)) (T.l (N.s N.z))

-- Now renaming types and constructors!
