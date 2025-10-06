-- import Mathlib
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

def helloWorld := "Hello world!"

#check helloWorld
-- hello : String

def theOldPond :=
  "An old silent pond\nA frog jumps into the pond—\nSplash! Silence again.\n"

#eval IO.println theOldPond
-- An old silent pond
-- A frog jumps into the pond—
-- Splash! Silence again.


def theOldPond' :=
"An old silent pond
A frog jumps into the pond—
Splash! Silence again.
"

#eval theOldPond'
-- "An old silent pond\nA frog jumps into the pond—\nSplash! Silence again.\n"

#eval "\n"
-- "\n"

#eval r"\n"
-- "\\n"

/-
With raw strings, backslashes are **not** interpreted as the beginning of a
special character.
-/

def theOldPond'' :=
  r"An old silent pond\nA frog jumps into the pond—\nSplash! Silence again.\n"

#eval IO.println theOldPond''
-- An old silent pond\nA frog jumps into the pond—\nSplash! Silence again.\n

/-
Quotes in quotes with raw strings, when augmented with hash marks:
-/

def pythonHelloWorld :=
r#"def main():
  print("Hello world!")
"#

#eval pythonHelloWorld
-- "def main():\n  print(\"Hello world!\")\n"

/-
### Concatenation
-/

#eval "Hello" ++ " " ++ "world!"
-- "Hello world!"

/-
### Conversion to String
-/

#check toString
-- ToString.toString.{u} {α : Type u} [self : ToString α] : α → String

#eval toString 42
-- "42"

#eval toString [1, 2, 3]
-- "[1, 2, 3]"

#eval toString 'A'
-- "A"

#eval toString "ABC"
-- "ABC"

/-
### String interpolation
-/

def name := "stranger"

#eval s!"Hello {name}!"
-- "Hello stranger!"

def answer := 42

#eval s!"The answer is {answer}"
-- The answer is 43

/-
### To/from list of characters
-/

#check helloWorld.data
-- helloWorld.data : List Char

#check helloWorld.toList
-- helloWorld.toList : List Char

#eval helloWorld.toList
-- ['H', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd', '!']

#eval String.mk ['A', 'B', 'C']
-- "ABC"

/-
### Length, random access, iteration
-/

#eval "ABC".length

#eval "ABC".toList[0]!
-- 'A'

def printChars (string : String) : IO Unit := do
  for char in string.toList do
     IO.print s!"{char} "

#eval printChars "Hello"
-- H e l l o

/-
### Slicing
-/

#eval helloWorld.drop 6
-- "world!"

#eval (helloWorld.drop 6).take 5
-- "world"

#eval helloWorld |>.drop 6 |>.take 5
-- "world"

/-
### Split, intercalate and trim
-/



#check String.splitOn
-- String.splitOn (s : String) (sep : String := " ") : List String

#eval helloWorld.splitOn " "
-- ["Hello", "world!"]

#eval " ".intercalate ["Hello", "world!"]
-- "Hello world!"

#eval theOldPond.splitOn "\n"
-- ["An old silent pond", "A frog jumps into the pond—", "Splash! Silence again.", ""]


#eval "         A B C  \n  ".trim
-- "A B C"

#eval theOldPond |>.trim |>.splitOn "\n"
-- ["An old silent pond\nA frog jumps into the pond—\nSplash! Silence again."]

/-
### Startswith and contains
-/

#eval helloWorld.startsWith "Hello"
-- true

#eval helloWorld.contains 'w'
-- true

#eval helloWorld.containsSubstr "world"
-- true

/-
### Kawai
-/

def String.isWhitespace (string : String) :=
  string |>.toList |>.all Char.isWhitespace

#eval "    \n    \t     ".isWhitespace
-- true

#eval "       A     ".isWhitespace
-- false

partial def String.leading (string : String) : Nat :=
  if !string.startsWith " " then
    0
  else
    (string |>.drop 1 |>.leading) + 1

def leadingAux (chars : List Char) : Nat :=
  match chars with
  | ' ' :: chars => (leadingAux chars) + 1
  | _ => 0

def String.leading' (string : String) : Nat :=
  leadingAux string.toList

#exact String.len

#eval "   A".leading
-- 3

def kawai (string : String) : String := Id.run do
  let lines := string.splitOn "\n"
  let lines := lines.filter (not ·.isWhitespace)
  if lines.isEmpty then
    return ""
  else
    let leading := lines[0]!.leading
    let lines := lines.map (·.drop leading)
    return "\n".intercalate lines

def theOldPond_3 := kawai "
  An old silent pond
  A frog jumps into the pond—
  Splash! Silence again.
"

#eval IO.println theOldPond_3
-- An old silent pond
-- A frog jumps into the pond—
-- Splash! Silence again.

def indents := kawai "
  A
    B
      C
"

#eval IO.println indents
-- A
--   B
--     C

/-
Tuples
--------------------------------------------------------------------------------
-/

def pair := ("answer", 42)

#check pair
-- String × Nat

def swap (pair : String × Nat) : Nat × String :=
  let (s, n) := pair
  (n, s)

#eval swap pair
-- (42, "answer")

def triple := ("answer", 42, true)

#check triple
-- String × Nat × Bool

#eval ("answer", (42, true))
-- String × Nat × Bool

#check String × (Nat × Bool)
-- String × Nat × Bool : Type

/-
Lists & Arrays
--------------------------------------------------------------------------------
-/

/-
### Lists

**TODO**
-/


/-
### Arrays

**TODO**

-/

def array := #[1, 2, 3]

#check array
-- array : Array Nat

#check Array.toList
-- Array.toList.{u} {α : Type u} (self : Array α) : List α

#eval array.toList
-- [1, 2, 3]

#check List.toArray
-- List.toArray.{u_1} {α : Type u_1} (xs : List α) : Array α

#eval [1, 2, 3].toArray
-- #[1, 2, 3]

/-
Associative Arrays & Hash Maps
--------------------------------------------------------------------------------

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
