

TODO:

  - start with structure?

  - add "methods" and "fields" to a structure

  - builtin methods for structures

  - add "enums"


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

```python

Lean lessons: exclusive and exhaustive (display pattern matching)

```lean
-- There are only two kinds of languages:
inductive LanguageKind where
  | onePeopleComplainAbout
  | oneNobodyUses
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
```

```lean
inductive L where
  | n : L
  | c (h : N) (t : L) : L -- or c : N -> L -> L
```

```lean
inductive T where
  | l (n : N) : T
  | b (l: T) (r : T) : T -- or b : T -> T -> T
```

Use, let example, maybe a fancy repr


TODO: fancy repr?

├── bin
│   ├── script.sh
│   └── util
│       └── helper.sh
└── README.md

  - add "GADTs"

  - add "dependent types"



  - nota: see that structures are actually a special case of inductive types

