/-
Source: https://parentheticallyspeaking.org/articles/fat-nums/

3 Things explored here, almost orthogonal:

  - New type (either structure or def as List Nat)
    Can be avoid to a large extent if we take directly
    List Nat as our type. Not very important here.
    And List Nat is pretty sweet here actually since any
    value of this type *is* a valid FatNum.

  - Many functions to define, most of them iterative or recursive.

  - Many examples of type classes.

-/


/-
Step 1
-/

structure FatNum where  -- Alternative: def FatNum := List Nat and define mk manually
  numbers : List Nat    -- Pro: no "partial" trick needed in toString

def FatNum.toList (fn : FatNum) : List Nat := fn.numbers

-- Auxiliary method to avoid the partial?
partial def FatNum.toString (fn : FatNum) : String :=
  match fn.numbers with
  | []                => ""
  | number :: []      => s!"{number} * 10^0"
  | number :: numbers =>
      s!"{number} * 10^{numbers.length} + " ++ FatNum.toString (FatNum.mk numbers)

#eval [99, 10, 7]
-- [99, 10, 7]

#eval (FatNum.mk [99, 10, 7]).toList
-- [99, 10, 7]

#eval (FatNum.mk [99, 10, 7]).toString
-- "99 * 10^2 + 10 * 10^1 + 7 * 10^0"



/-
Step 2
-/

instance : ToString FatNum where
  toString := FatNum.toString

instance : Repr FatNum where
  reprPrec fn _ := toString fn

#eval FatNum.mk [99, 10, 7]
-- 99 * 10^2 + 10 * 10^1 + 7 * 10^0

/-
Step 3
-/

def FatNum.pad (p : Nat) (fn : FatNum) : FatNum :=
  let m : Nat := p - fn.toList.length
  FatNum.mk ((List.replicate m 0) ++ fn.numbers)

#eval (FatNum.mk [99, 10, 7]).pad 5
-- 0 * 10^4 + 0 * 10^3 + 99 * 10^2 + 10 * 10^1 + 7 * 10^0

def FatNum.add (fm fn : FatNum) : FatNum :=
  let length := max fm.toList.length fn.toList.length
  let fn := fn.pad length
  let fm := fm.pad length
  List.zip fn.toList fm.toList |>.map (fun (a, b) => a + b) |> FatNum.mk

#eval FatNum.add (FatNum.mk [1, 0, 1, 0]) (FatNum.mk [1, 2, 3])
-- 1 * 10^3 + 1 * 10^2 + 3 * 10^1 + 3 * 10^0

/-
Step 4
-/

instance : Add FatNum where
  add := FatNum.add

#eval (FatNum.mk [1, 0, 1, 0]) + (FatNum.mk [1, 2, 3])
-- 1 * 10^3 + 1 * 10^2 + 3 * 10^1 + 3 * 10^0

/-
Step 5
-/

def FatNum.mul (fm fn : FatNum) : FatNum := Id.run do
  let mut product := FatNum.mk []
  for (number, i) in fm.toList.reverse.zipIdx do
    let extra := fn.numbers
      |>.map (number * ·)
      |> (· ++ List.replicate i 0)
      |> FatNum.mk
    product := product + extra
  return product

instance : Mul FatNum where
  mul := FatNum.mul

#eval (FatNum.mk [4, 2, 1]) * (FatNum.mk [0])
-- 0 * 10^2 + 0 * 10^1 + 0 * 10^0

#eval (FatNum.mk [4, 2, 1]) * (FatNum.mk [1])
-- 4 * 10^2 + 2 * 10^1 + 1 * 10^0

#eval (FatNum.mk [4, 2, 1]) * (FatNum.mk [2, 0])
-- 8 * 10^3 + 4 * 10^2 + 2 * 10^1 + 0 * 10^0

#eval (FatNum.mk [4, 2, 1]) * (FatNum.mk [2, 1])
-- 8 * 10^3 + 8 * 10^2 + 4 * 10^1 + 1 * 10^0

/-
Step 6
-/

def divMod (m n : Nat) : Nat × Nat := (m / n, m % n)

-- TODO: we need to "trim" the extra zeros to have a canonical repr.
def FatNum.shiftCarry (numbers : List Nat) : List Nat := Id.run do
  let numbers := numbers.reverse
  let mut normalized : List Nat :=  []
  let mut i := 0
  let mut carry := 0
  while carry > 0 || i < numbers.length do
    let number := carry +
      match numbers[i]? with
      | none => 0
      | some n => n
    normalized := normalized.concat (number % 10)
    carry := number / 10
    i := i + 1
  return normalized.reverse

def FatNum.trim (numbers : List Nat) : List Nat :=
  match numbers with
  | 0 :: numbers => FatNum.trim numbers
  | numbers => numbers

-- TODO: functional version?

def FatNum.normalize (fn : FatNum) : FatNum :=
    fn |>.toList |> FatNum.shiftCarry |> FatNum.trim |> FatNum.mk

#eval (FatNum.mk [99, 10, 7]).normalize
-- 1 * 10^4 + 0 * 10^3 + 0 * 10^2 + 0 * 10^1 + 7 * 10^0

#eval (FatNum.mk [4, 2, 1]).normalize
-- 4 * 10^2 + 2 * 10^1 + 1 * 10^0

#eval (FatNum.mk [421]).normalize
-- 4 * 10^2 + 2 * 10^1 + 1 * 10^0

#eval (FatNum.mk [0, 0, 0, 42]).normalize
-- 4 * 10^1 + 2 * 10^0

#eval (FatNum.mk [0, 0, 0, 0]).normalize
--

/- Step 7 -/

/- Issue with empty list of numbers?
No, that works perfectly. One may only question its string
representation, but even then, I think that's quite all right. -/

instance : BEq FatNum where
  beq fn fm := fn.normalize.toList == fm.normalize.toList

#eval FatNum.mk [4, 2, 1] == FatNum.mk [421]
-- true

#eval FatNum.mk [] == FatNum.mk [0]
-- true

#eval FatNum.mk [1, 0, 0] == FatNum.mk [1]
-- false

-- TODO: Nat <-> FatNum conversions.

def FatNum.ofNat (n : Nat) : FatNum :=
  FatNum.mk [n]

attribute [coe] FatNum.ofNat

instance : Coe Nat FatNum where
  coe := FatNum.ofNat

#eval id (α := FatNum) (id (α := Nat) 42)
-- 42 * 10^0

instance {n : Nat} : OfNat FatNum n where
  ofNat := n

#eval id (α := FatNum) 42
-- 42 * 10^0

def FatNum.toNat (fn : FatNum) : Nat :=
  fn.numbers.foldl (· * 10 + ·) 0

instance : Coe FatNum Nat where
  coe := FatNum.toNat

#eval @id (α := Nat) (FatNum.mk [1, 2, 3])
-- 123

#eval @id (α := Nat) (FatNum.mk [99, 10, 7])
-- 10007

/-
Step ???
-/

def FatNum.default : FatNum := FatNum.mk []

#eval FatNum.default.toList
-- []

instance : Inhabited FatNum where
  default := FatNum.default

def defaultFatNum : FatNum := default

#eval defaultFatNum.toList
-- []
