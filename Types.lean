
import Std
import Batteries

/-
Booleans
--------------------------------------------------------------------------------
-/

#check false
-- Bool.false : Bool

#check true
-- Bool.true: Bool

#eval !false
-- true

#eval !true
-- false

#check not
-- Bool.not: Bool -> Bool

#eval not false
-- true

#eval not true
-- false

#check and
-- Bool.and (x y : Bool) : Bool

#eval Bool.and true true
-- true

#eval true.and true
-- true

#eval true && true
-- true

#check or
-- Bool.or (x y : Bool) : Bool

#eval Bool.or false true
-- true

#eval false.or true
-- true

#eval false || true
-- true

/-
Numerical Types
--------------------------------------------------------------------------------
-/

def n := -1

#check n
-- n : Int

def p : Int := 42 -- force to be signed
-- p : Int

#eval (n * n + 1 % 3) ^ 2 / 2
-- 2

def m := 1

#check m
-- m : Nat

#eval m + 1
-- 2

#eval m - 42
-- 0

def x := 2.71

#check x
-- Float

#eval Float.log x
-- 0.996949

#eval x.log
-- 0.996949

#eval Float.log 0
-- -inf

#eval Float.log (-1)
-- NaN

#eval Float.inf
-- inf

#eval Float.nan
-- NaN



/-
Characters
--------------------------------------------------------------------------------
-/

def char := 'A'

#check char
-- char : Char

#eval IO.println char
-- A

#eval char.toNat
-- 65

def wave := '👋'

#check wave
-- wave : Char

#eval wave.toNat
-- 128075

#eval IO.println wave
-- 👋

/-
Strings
--------------------------------------------------------------------------------
-/

def hello := "Hello world!"

#check hello
-- hello : String

#eval "Hello" ++ " " ++ "world!"
-- "Hello world!"

def name := "stranger"

#eval s!"Hello {name}!"
-- "Hello stranger!"

/-
TODO:
  - to/from list of chars
  - iteration (directly?)
  - length, slicing
  - startsWith, contains
  - trim
  - splitlines
-/

/-
Tuples
--------------------------------------------------------------------------------
-/

/-
Lists & Arrays
--------------------------------------------------------------------------------
-/

/-
Associative Arrays & Hash Maps
--------------------------------------------------------------------------------
-/

/-
Similar to dictionaries in Python.

⚠️  Dictionaries are used **everywhere** in Python, but associative arrays and
hash maps are not that common in Lean code. Why? Because one of the use cases
of dictionaries in Python is the description of a fixed data structure that
associates a fixed list of string indentifiers and some typed values.
And for this use case, it's worth defining a new `structure` in Lean
instead of using associative arrays or Hash Maps, since the compiler
will issue all kinds of errors when the structure is not correct.

You can think of it that way:
if you can transform your Python dictionary to a a [data class],
then define a new Lean structure.

[data class]: https://docs.python.org/3/library/dataclasses.html
-/

/-
### Structures

Source: 🐍 <https://docs.python.org/3/library/dataclasses.html>

```python
from dataclasses import dataclass

@dataclass
class InventoryItem:
    """Class for keeping track of an item in inventory."""
    name: str
    unit_price: float
    quantity_on_hand: int = 0

    def total_cost(self) -> float:
        return self.unit_price * self.quantity_on_hand
```
-/

/- Structure for keeping track of an item in inventory. -/
structure InventoryItem where
  name : String
  unitPrice : Float
  quantityOnHand : Nat := 0

def InventoryItem.totalCost (item : InventoryItem) : Float :=
  item.unitPrice * item.quantityOnHand.toFloat


def apples : InventoryItem := {
  name := "apple",
  unitPrice := 3.0,
  quantityOnHand := 6,
}

#eval apples.quantityOnHand
-- 6

def apples' : InventoryItem := { apples with quantityOnHand := 3 }

#eval apples'
-- { name := "apple", unitPrice := 3.000000, quantityOnHand := 3 }

/-
### Associative Arrays

DIY associative arrays as lists of key-value pairs.

-/

abbrev NumbersDict := List (String × Nat)

def numbersDict : NumbersDict := [("one", 1), ("two", 2), ("three", 3)]

def set (dict : NumbersDict) (key : String) (value : Nat) : NumbersDict :=
  (key, value) :: dict

def get! (dict : NumbersDict) (key : String) := Id.run do
  for (k, v) in dict do
    if k == key then
      return v
  panic! s!"Invalid key {key}"

#eval get! numbersDict "two"
-- 2

#eval get! numbersDict "four"
-- PANIC at get! Types:114:2: Invalid key four

def numbersDict' := set numbersDict "four" 4

#eval get! numbersDict' "four"
-- 4

/-
### HashMap

-/

abbrev NumDict := Std.HashMap String Nat

def numDict := Std.HashMap.ofList [("one", 1), ("two", 2), ("three", 3)]

#eval numDict
-- Std.HashMap.ofList [("three", 3), ("two", 2), ("one", 1)]

def display (numDict: NumDict) : IO Unit := do
  for kv in numDict do
    IO.println kv

#eval display numDict
-- (three, 3)
-- (two, 2)
-- (one, 1)

def numDict' : NumDict :=
  ((({} : NumDict).insert "one" 1).insert "two" 2).insert "three" 3

#eval display numDict'

#eval numDict.get! "one"

#eval numDict.get! "four"
-- PANIC at Std.DHashMap.Internal.AssocList.get!
-- Std.Data.DHashMap.Internal.AssocList.Basic:142:11: key is not present in hash table

#eval (numDict.insert "one" 111).get! "one"
--- 111

#eval display (numDict.insert "one" 111)
-- (three, 3)
-- (two, 2)
-- (one, 111)

#check hash
-- Hashable.hash.{u} {α : Sort u} [self : Hashable α] : α → UInt64

#eval hash "one"
-- 17970580055335648935
