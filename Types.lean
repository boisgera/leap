
import Std

/-
Booleans
--------------------------------------------------------------------------------
-/

/-
Integers
--------------------------------------------------------------------------------
-/

/-
Characters
--------------------------------------------------------------------------------
-/

/-
Strings
--------------------------------------------------------------------------------
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
