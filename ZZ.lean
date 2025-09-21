


structure ZZ where -- Zigzag signed integer
  i : Nat -- 0 -> 0, 1 -> -1, 2 -> 1, 3 -> -2, ...
deriving BEq

def ZZ.toInt (z : ZZ) : Int :=
  let d := Int.ofNat (z.i / 2)
  let r := (z.i % 2) != 0
  match r with
  | false => d
  | true => - d - 1

def ZZ.toString (z : ZZ) : String :=
  ToString.toString z.toInt

instance : ToString ZZ where
  toString := ZZ.toString

#eval ZZ.mk 0
-- 0

#eval ZZ.mk 1
-- -1

#eval ZZ.mk 2
-- 1

#eval ZZ.mk 3
-- -2

def ZZ.ofInt (n : Int) : ZZ :=
  if n.sign == 0 then
    ZZ.mk 0
  else if n.sign == 1 then
    ZZ.mk (2 * n).toNat
  else
    ZZ.mk (-2 * n - 1).toNat

#eval ZZ.ofInt 0
-- 0

#eval ZZ.ofInt 1
-- 1

#eval ZZ.ofInt 2
-- 2

#eval ZZ.ofInt (-1)
-- -1

#eval ZZ.ofInt (-2)
-- -2


partial def ZZ.sign (z : ZZ) : ZZ :=
  match z.i with
  | 0 => ZZ.mk 0
  | 1 => ZZ.mk 1
  | 2 => ZZ.mk 2
  | n + 2 => (ZZ.mk n).sign

#eval (ZZ.ofInt 0).sign
-- 0
#eval (ZZ.ofInt 1).sign
-- 1
#eval (ZZ.ofInt 42).sign
-- 1
#eval (ZZ.ofInt (-1)).sign
-- -1
#eval (ZZ.ofInt (-7)).sign
-- -1

def ZZ.abs (z : ZZ) : Nat := (z.i + 1) / 2

#eval 0 |> ZZ.ofInt |>.abs
-- 0
#eval 7 |> ZZ.ofInt |>.abs
-- 7
#eval (-7) |> ZZ.ofInt |>.abs
-- 7

def ZZ.neg (z : ZZ) : ZZ :=
  if z.sign == (ZZ.ofInt 0) then
    ZZ.mk 0
  else if z.sign == (ZZ.ofInt 1) then
    ZZ.mk (z.i  - 1)
  else
    ZZ.mk (z.i + 1)

instance : Neg ZZ where
  neg := ZZ.neg

#eval - (ZZ.ofInt 0)
-- 0
#eval - (ZZ.ofInt 1)
-- -1
#eval - (ZZ.ofInt (-1))
-- 1
#eval - (ZZ.ofInt (7))
-- -7
#eval - (ZZ.ofInt (-7))
-- 7

def ZZ.succ (z : ZZ) : ZZ :=
  match z.i with
  | 1 => ZZ.mk 0
  | i =>
    if z.sign == (ZZ.ofInt 0) || z.sign == (ZZ.ofInt 1) then
      ZZ.mk (i + 2)
    else
      ZZ.mk (i - 2)

#eval 0 |> ZZ.ofInt |>.succ
-- 0
#eval -1 |> ZZ.ofInt |>.succ
-- 0
#eval 1 |> ZZ.ofInt |>.succ
-- 0
#eval -2 |> ZZ.ofInt |>.succ
-- 0
#eval 2 |> ZZ.ofInt |>.succ
-- 3

-- No smart way to do this? Pattern matching or recursion?
-- I mean we can do recursion, but there is still an awful lot
-- of cases to consider...
def ZZ.add (z z' : ZZ) : ZZ :=
  sorry

def ZZ.mul (z z' : ZZ) : ZZ :=
  sorry

-- TODO: show some properties of the ring structure?
