
Product Types
--------------------------------------------------------------------------------

## Tuples


```lean
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
```

So there is not really a n-uple for n>=2, and no 1-uple or 0-uple either.
Only pairs, and nested pairs!

```lean
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
```

Sum Types
--------------------------------------------------------------------------------

```lean
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
```

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


```lean
-- There are only two kinds of languages:

inductive LanguageKind where
| theOnesPeopleComplainAbout
| theOnesNobodyUses
```

## parametrized enums


```rust
enum Shape {
    Point,
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 }
}
```



## Recursive (/inductive) enums aka algebraic data types

```rust
enum List {
    Nil,
    Cons(i32, Box<List>),
}
```


## Algebraic data types

### What is `B`?


```lean
inductive B where
  | f : B
  | t : B
deriving Repr -- for convenience

#check B
-- B : Type
```

The new type `B` has two **constructors** `B.f` and `B.t`.

```lean
#check B.f
-- B.f : B

#eval B.f
-- B.f

#check B.t
-- t : B

#eval B.t
-- B.t
```

Since constructors have to deliver a value of type `B`,
the declaration of the type of `f` and `t` is actually optional.

```lean
inductive B' where
  | f
  | t
```

This list of constructors is exhaustive and exclusive, meaning that

  - every value of type `B` is either `B.f` or `B.t`

  - no value can be both.


So our `B` type is isomorphic to the `Bool` type, with `B.f`
corresponding to `false` and `B.t` to `true`.


Handling of inductive types is done by pattern matching.

```lean
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
```

### What is `O`?

The constructors of an inductive type can take arguments.

```lean
inductive O where
  | n : O
  | s (b : B) : O
deriving Repr -- for convenience
```

Alternatively, the terser:

```lean
inductive O' where
  | n
  | s (b : B)
```

To create values of type `O`, we use the constructors:

```lean
#eval O.n
-- O.n

#eval O.s B.f
-- O.s (B.f)

#eval O.s B.t
-- O.s (B.t)
```

This is the complete list of values of type `O` that you can create,
and they are all distinct.

Here `O` represents an option type: a value of type is either one
of the value of type `B` (i.e. false, true), or nothing ("undefined").

With this in mind, we could reimplement our version of `not` and `and`
for this type:

```lean
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
```

We have designed an option type for booleans, but we could do the same
for any type `α`. Here is a parametrized version of `O`.

```lean
inductive OP (α : Type) where
  | n : OP α
  | s (a : α) : OP α
deriving Repr -- for convenience

def O_B := OP B

def O_Nat := OP Nat

def n : O_Nat := OP.n

#eval n
-- OP.n

def n' : O_Nat := OP.s 42

#eval n'
-- OP.s 42
```

### What is `N`?

Our first example which is actually recursive!

```lean
inductive N where
  | z : N
  | s (n : N) : N
```

Alternatively, the terser:

```lean
inductive N' where
  | z
  | s (n : N')
```

or the variant that makes the type of each constructor explicit:

```lean
inductive N'' where
  | z : N''
  | s : N'' -> N''
deriving Repr -- for convenience
```

What these definitions say is that a value of type `N` is either

  - the constructor `N.z`, or

  - the constructor `N.s` applied to another (pre-existing) value of type `N`.

```lean
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

#eval N.z |>.s |>.s |>.s
-- N.s (N.s (N.s (N.z)))
```

What we have here is a representation of natural numbers! With `N.z` being
the zero and `N.s` being the successor function (i.e. `+1`).

```lean
def zero := N.z
def succ := N.s
```

That's enough to define the usual arithmetic operations:

```lean
def add (n1 n2 : N) : N :=
  match n1 with
  | N.z => n2
  | N.s m => N.s (add m n2)

#eval add (N.z.s.s) (N.z.s.s.s)
-- N.s (N.s (N.s (N.s (N.s (N.z)))))

def mul (n1 n2 : N) : N :=
  match n1 with
  | N.z => N.z
  | N.s m => add n2 (mul m n2)
```

### What is `L`?

```lean
inductive L where
  | n : L
  | c (h : Nat) (t : L) : L

inductive L' where
  | n
  | c (h : Nat)

inductive L'' where
  | n : L''
  | c : Nat -> L'' -> L''

#eval L.n
-- L.n

#eval L.c 42 L.n
-- L.c 42 (L.n)

#eval L.c 1 (L.c 2 (L.c 3 L.n))
-- L.c 1 (L.c 2 (L.c 3 (L.n)))
```

Yes, that's a linked list of natural numbers!

```lean
def L.length : L -> Nat
  | L.n        => 0
  | L.c _ tail => (L.length tail) + 1

def L.get! : L -> Nat -> Nat
  | L.n, _ => panic! "index out of bounds"
  | L.c head _tail, 0 => head
  | L.c _head tail, Nat.succ i => tail.get! i


#check List.concat
-- List.concat.{u} {α : Type u} : List α -> α -> List α


def L.concat : L -> Nat -> L
  | L.n          , x => L.c x L.n
  | L.c head tail, xs => L.c head (tail.concat xs)


#check List.append
-- List.append.{u} {α : Type u} (xs ys : List α) : List α

def L.append : L -> L -> L
  | L.n     , ys => ys
  | L.c x xs, ys => L.c x (xs.append ys)
```

General / parametrized version of `L`:

```lean
inductive LP (α : Type) where
  | n : LP α
  | c (h : α) (t : LP α) : LP α
```

### What is `T`?

```lean
inductive T (α : Type u) where
  | l (a : α) : T α
  | b (a : α) (l : T α) (r : T α) : T α
deriving Repr

inductive T' (α : Type u) where
  | l (n : N)
  | b (a : α) (l: T α) (r : T α)

inductive T'' (α : Type) where
  | l : N -> T'' α
  | b : α -> T'' α -> T'' α -> T'' α
```

Note: with this description, we can't have empty trees.

```lean
def exampleTree : T Nat :=
  T.b 0 (T.b 1 (T.l 2) (T.l 3)) (T.l 4)

#eval exampleTree
-- T.b 0 (T.b 1 (T.l 2) (T.l 3)) (T.l 4)


def T.depth.{u} {α : Type u} (tree : T α) :=
  match tree with
  | l _ => 1
  | b _ b1 b2 => 1 + max b1.depth b2.depth

#eval exampleTree.depth
-- 3
```

Alternative definition (!=, but related)

```lean
inductive Tree (α : Type u) where
  | empty : Tree α
  | branch : α -> Tree α -> Tree α -> Tree α
```

With this definition, we have a mapping that associates to any finite
sequence of booleans (which encode a left-right path) an element of
type α or nothing, such that if the element associated to a path is not
nothing, then it's also no nothing for any prefix.

```lean
def Tree.get {α} (tree : Tree α) (path : List Bool) : Option α :=
  match tree, path with
  | empty         , _  => none
  | branch a  _  _, [] => a
  | branch _ b1  _, false :: path => b1.get path
  | branch _  _ b2, true :: path  => b2.get path
```

### **Generalized** Algebraic Data Types

According to their [Wikipedia page](https://en.wikipedia.org/wiki/Generalized_algebraic_data_type):

> In a GADT, the [...] constructors can provide an explicit instantiation
> of the ADT as the type instantiation of their return value.

Let's illustrate this with a design of a small expression language made of
bools, natural numbers, comparison for equality, an if-then-else construct
and let's say not, and and add.


```lean
inductive Expr : Type -> Type where
  | bool : Bool -> Expr Bool
  | nat : Nat -> Expr Nat
  | not : Expr Bool -> Expr Bool
  | and : Expr Bool -> Expr Bool -> Expr Bool
  | add : Expr Nat -> Expr Nat -> Expr Nat
  | eq : Expr Nat -> Expr Nat -> Expr Bool
  | ite : Expr Bool -> Expr Nat -> Expr Nat -> Expr Nat

def Expr.toString {α} (expr : Expr α) : String :=
  match expr with
    | bool b => ToString.toString b
    | nat n => ToString.toString n
    | not e => s!"(not {e.toString})"
    | and e f => s!"({e.toString} and {f.toString})"
    | add m n => s!"({m.toString} + {n.toString})"
    | eq m n => s!"({m.toString} == {n.toString})"
    | ite b e f => s!"(if {b.toString} then {e.toString} else {f.toString})"

#eval Expr.not (Expr.and (Expr.bool false) (Expr.bool true)) |>.toString
-- "(not (false and true))"

#eval Expr.ite (Expr.eq (Expr.add (Expr.nat 1) (Expr.nat 1)) (Expr.nat 2)) (Expr.nat 1) (Expr.nat 0) |>.toString
-- "(if ((1 + 1) == 2) then 1 else 0)"

def Expr.eval {α} (expr : Expr α) : α :=
  match expr with
    | bool b => b
    | nat n => n
    | not e => Bool.not e.eval
    | and e f => Bool.and e.eval f.eval
    | add m n => Nat.add m.eval n.eval
    | eq m n => m.eval == n.eval
    | ite b e f => if b.eval then e.eval else f.eval

#eval Expr.not (Expr.and (Expr.bool false) (Expr.bool true)) |>.eval
-- true

#eval Expr.ite (Expr.eq (Expr.add (Expr.nat 1) (Expr.nat 1)) (Expr.nat 2)) (Expr.nat 1) (Expr.nat 0) |>.eval
-- 1
```
