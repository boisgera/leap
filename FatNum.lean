/-
Source: https://parentheticallyspeaking.org/articles/fat-nums/
-/


/-
Step 1
-/

structure FatNum where  -- Alternative: def FatNum := List Nat and define mk manually
  numbers : List Nat    -- Pro: no "partial" trick needed in toString

def FatNum.toList (fn : FatNum) : List Nat := fn.numbers

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
  reprPrec p _ := toString p

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

def FatNum.normalizeAux (numbers : List Nat) : List Nat := Id.run do
  let mut numbers := numbers.reverse
  repeat
    numbers := match numbers with
    | []           => []
    | n :: []      => if n >= 10 then [n % 10, n / 10] else [n]
    | n :: m :: ns => (n % 10) :: (n / 10 + m) :: ns
  -- stopping condition?
  return numbers.reverse

-- partial def FatNum.normalizeAux' (numbers : List Nat) : List Nat :=
--   match _: numbers with
--     | [] => []
--     | [n] => if n > 10 then [n / 10, n % 10] else [n]
--     | n :: ns => match normalizeAux ns with
--       | [] => unreachable!
--       | head::tail => normalizeAux ([n + head]) ++ tail

def FatNum.normalize (fn : FatNum) : FatNum :=
    fn |>.toList |> FatNum.normalizeAux |> FatNum.mk
