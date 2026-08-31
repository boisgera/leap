

namespace SafeArithmetic

def add (m n : Nat) : Option Nat :=
  some (m + n)

def sub (m n : Nat) : Option Nat :=
  if m ≥ n then
    some (m - n)
  else
    none

def div (m n : Nat) : Option Nat :=
  if n ≠ 0 then
    m / n
  else
    none

def mod (m  n : Nat) : Option Nat :=
  if n ≠ 0 then
    m % n
  else
    none

def f (m n : Nat) : Option Nat :=
  -- (m - n) / (m + n)
  let num? := sub m n
  let den? := add m n
  match num? with
  | some num =>
    match den? with
    | some den => div num den
    | none => none
  | none => none


#print Option.bind
-- @[implicit_reducible] protected def Option.bind.{u_1, u_2} : {α : Type u_1} →
--   {β : Type u_2} → Option α → (α → Option β) → Option β :=
-- fun {α} {β} x x_1 =>
--   match x, x_1 with
--   | none, x => none
--   | some a, f => f a

def f' (m n : Nat) : Option Nat :=
  let num? := sub m n
  num?.bind fun num =>
    let den? := add m n
    den?.bind fun den =>
      div num den

def f'' (m n : Nat) : Option Nat :=
  let num? := sub m n
  num? >>= fun num =>
    let den? := add m n
    den? >>= fun den =>
      div num den

def f''' (m n : Nat) : Option Nat := do
  let num <- sub m n
  let den <- add m n
  div num den

end SafeArithmetic
