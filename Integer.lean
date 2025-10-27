import Mathlib

#print Int
-- inductive Int : Type
-- number of parameters: 0
-- constructors:
-- Int.ofNat : Nat → Int
-- Int.negSucc : Nat → Int

inductive Integer where
| ofNat : Nat -> Integer
| negSucc : Nat -> Integer

instance {n : Nat} : OfNat Integer n where
  ofNat := Integer.ofNat n

/--
info: Integer.ofNat 0
-/
#guard_msgs in
#eval (0 : Integer)

/--
info: Integer.ofNat 1
-/
#guard_msgs in
#eval (1 : Integer)


-- Reinvestigate, code golf, etc. Then have a look at DecidableEq?
-- and have a look at the actual implementation of this stuff for Int
instance {m n : Integer} : Decidable (m = n) :=
  open Integer in
  match m, n with
  | ofNat m, ofNat n =>
      match decEq m n with
      | isFalse h =>
          have h' : ¬Integer.ofNat m = Integer.ofNat n := by
            intro h''
            have nc := Integer.noConfusion h'' id
            exact h nc
          isFalse h'
      | isTrue h => isTrue (congrArg Integer.ofNat h)
  | ofNat m, negSucc n => isFalse Integer.noConfusion
  | negSucc m, ofNat n => isFalse Integer.noConfusion
  | negSucc m, negSucc n =>
      match decEq m n with
      | isFalse h =>
          have h' : ¬Integer.negSucc m = Integer.negSucc n := by
            intro h''
            have nc := Integer.noConfusion h'' id
            exact h nc
          isFalse h'
      | isTrue h => isTrue (congrArg Integer.negSucc h)

-- @[extern "lean_int_dec_eq"]
-- protected def decEq (a b : @& Int) : Decidable (a = b) :=
--   match a, b with
--   | ofNat a, ofNat b => match decEq a b with
--     | isTrue h  => isTrue  <| h ▸ rfl
--     | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)
--   | ofNat _, -[_ +1] => isFalse <| fun h => Int.noConfusion h
--   | -[_ +1], ofNat _ => isFalse <| fun h => Int.noConfusion h
--   | -[a +1], -[b +1] => match decEq a b with
--     | isTrue h  => isTrue  <| h ▸ rfl
--     | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)



def Integer.toString : Integer -> String
| ofNat n => ToString.toString n
| negSucc n => "-" ++ ToString.toString (n + 1)

instance : ToString Integer where
  toString := Integer.toString

#eval do assert! toString (Integer.ofNat 2) == "2"
#eval do assert! toString (Integer.ofNat 1) == "1"
#eval do assert! toString (Integer.ofNat 0) == "0"
#eval do assert! toString (Integer.negSucc 0) == "-1"
#eval do assert! toString (Integer.negSucc 1) == "-2"

instance : Repr Integer where
  reprPrec n _ := Integer.toString n

def Integer.beq (m n : Integer) : Bool :=
  match m, n with
  | ofNat m, ofNat n => m == n
  | negSucc m, negSucc n => m == n
  | _, _ => false

instance : BEq Integer where
  beq := Integer.beq

-- Nota: I'd like to use symmetry in the third case, but that involves
--       recursivity and Lean doesn't know that "it works" by default
def Integer.add (m n : Integer) : Integer :=
  match m, n with
  | ofNat m, ofNat n => ofNat (m + n)
  | ofNat m, negSucc n =>
      if m >= n + 1 then
        ofNat (m - n - 1)
      else
        negSucc (n - m)
  | negSucc m, ofNat n =>
      if n >= m + 1 then
        ofNat (n - m - 1)
      else
        negSucc (m - n)
  | negSucc m, negSucc n => negSucc (m + n + 1)

instance : Add Integer where
  add := Integer.add

#eval do assert! Integer.ofNat 1 + Integer.ofNat 2 == Integer.ofNat 3
#eval do assert! Integer.ofNat 1 + Integer.negSucc 0 == Integer.ofNat 0
#eval do assert! Integer.ofNat 1 + Integer.negSucc 1 == Integer.negSucc 0
#eval do assert! Integer.negSucc 1 + Integer.negSucc 2 == Integer.negSucc 4

def Integer.neg (n : Integer) : Integer :=
  match n with
  | Integer.ofNat 0 => ofNat 0
  | Integer.ofNat (n + 1) => negSucc n
  | Integer.negSucc n => ofNat (n + 1)

instance : Neg Integer where
  neg := Integer.neg

def Integer.sub (m n : Integer) : Integer :=
  m + (-n)
