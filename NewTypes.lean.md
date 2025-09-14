
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
--/
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


### Mysterious examples : Nat, List and Tree in disguise


```lean
inductive N where
  | z : N
  | s (n : N) : N



inductive L where
  | n : L
  | c (h : N) (t : L) : L -- or c : N -> L -> L



inductive T where
  | l (n : N) : T
  | b (l: T) (r : T) : T -- or b : T -> T -> T
```

```lean
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
```
