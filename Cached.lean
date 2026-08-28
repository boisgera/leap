import Std


def memoize {α β} [BEq α] [Hashable α] (f : α -> β) (a : α) :
      (Std.HashMap α β) -> β × (Std.HashMap α β) :=
    fun cache => match cache.get? α with
      | some b =>
        (b, cache)
      | none =>
        let b := f a
        (b, cache.insert a b)

namespace Crypto

abbrev Hash := UInt64

def Hash.toBools (hash : Hash) : List Bool :=
  let shift (i : Nat) : UInt64 := (hash >>> UInt64.ofNat (63 - i)) &&& 1
  let bools := (List.range 64).map (fun i => shift i == 1)
  bools

-- Human-readable 64-bit binary string, for inspection/debugging.
def Hash.toString (hash : Hash) : String :=
  let chars := hash.toBools.map fun b =>
    match b with
    | false => '0'
    | true => '1'
  String.ofList chars

#eval (2^64 - 1 : Hash).toString
-- "1000000000000000000000000000000000000000000000000000000000000000"

#eval (2^63 - 1 : Hash).toString
-- "0100000000000000000000000000000000000000000000000000000000000000"

#eval (42 : Hash).toString
-- "0000000000000000000000000000000000000000000000000000000000100000"

-- Count leading zero bits in the 64-bit representation of a hash.
def Hash.leadingZeros (hash : Hash) : Nat :=
  let hashBools := hash.toBools
  let firstTrueIndex := (List.range 64).find? (fun i => hashBools[i]! == true)
  firstTrueIndex.getD 64

#eval Hash.leadingZeros (2 ^ 64 - 1)
-- 0

#eval Hash.leadingZeros (2 ^ 63 - 1)
-- 1

#eval Hash.leadingZeros 42
-- 58

#eval Hash.leadingZeros 1
-- 63

#eval Hash.leadingZeros 0
-- 64

-- Search for a nonce `n` such that `hash(msg ++ toString n)` has
-- at least `difficulty` leading zero bits.
-- Returns `none` if no such `nonce` is found within `maxNonce` attempts.
def mine (msg : String) (difficulty : Nat)
    (maxNonce : Nat := 10_000_000) (nonce : Nat := 0)
    : Option String :=
  if nonce ≥ maxNonce then
    none
  else
    let candidate := msg ++ toString nonce
    let hash : Hash := hash candidate
    if hash.leadingZeros ≥ difficulty then
      some candidate
    else
      mine msg difficulty maxNonce (nonce + 1)

#time -- time: 233ms
#eval
  match mine "Hello crypto!" (difficulty := 16) with
  | some solution => solution
  | none => ""
-- "Hello crypto!5030"


-- AAAAAAH FUCK, I would need to memoize wrt the first three args
-- and therefore use a non-idiomatic version of the mine signature...
-- TODO: implement the cached version MANUALLY. That is also going to
-- simplify the signature (no more genericity needed).
def memoMine := memoize mine
-- Crypto.memoMine (a : String) :
--   Std.HashMap String (Nat → Option String) → (Nat → Option String) × Std.HashMap String (Nat → Option String)

abbrev Cache := Std.HashMap String String -- message -> solution

def cachedMine (msg : String) (difficulty : Nat)
    (maxNonce : Nat := 10_000_000) (nonce : Nat := 0)
    (cache : Cache := {})
    : (Option String) × Cache :=

  -- Hopefully, there is a cached solution and it works for us.
  let cachedSolution : Option String := match cache.get? msg with
  | some solution =>
    let leadingZeros := Hash.leadingZeros (hash solution)
    if leadingZeros ≥ difficulty then
      some solution
    else
      none
  | none => none

  match cachedSolution with
  | some solution => (solution, cache)
  | none => match mine msg difficulty maxNonce nonce with
    | some solution => (some solution, cache.insert msg solution)
    | none => (none, cache)

#time
#eval do
  let result := mine "Hello crypto!" (difficulty := 17)
  IO.println <| result

#time
#eval do
  let result := mine "Hello crypto!" (difficulty := 16)
  IO.println <| result
  let result := mine "Hello crypto!" (difficulty := 15)
  IO.println <| result

#time
#eval do
  let (result, cache) := cachedMine "Hello crypto!" (difficulty := 17)
  IO.println <| result
  IO.println <| repr cache

#time
#eval do
  let (result, cache) := cachedMine "Hello crypto!" (difficulty := 16)
  IO.println <| result
  IO.println <| repr cache
  let (result, cache) := cachedMine "Hello crypto!" (difficulty := 15) (cache := cache)
  IO.println <| result
  IO.println <| repr cache

end Crypto

namespace Collatz

def step (n : Nat) : Nat :=
  if n % 2 == 0 then
    n / 2
  else
    3 * n + 1

-- We can't return a Unit, we risk the function being optimized away!
partial def loop (n : Nat) : Bool :=
  -- dbg_trace n
  if n == 1 then
    -- dbg_trace "---"
    true
  else
    loop (step n)

def checkRange (n : Nat) : List Bool :=
  let range := n |> List.range |>.map (· + 1)
  range.map loop

#time -- 11 ms
#eval checkRange 100 |>.all (· == true)
-- true

#time -- 74 ms
#eval checkRange 1_000 |>.all (· == true)
-- true

#time -- 944 ms
#eval checkRange 10_000 |>.all (· == true)
-- true

#time -- 13161 ms
#eval checkRange 100_000 |>.all (· == true)
-- true

/-
Shoot, implementing a cache on this is complex because the function is recursive
-/


partial def cachedLoop (n : Nat) (cache : Std.HashMap Nat Bool := {}) :
    Bool × (Std.HashMap Nat Bool) :=
  if cache.contains n then
    (true, cache)
  else if n = 1 then
    (true, cache.insert 1 true)
  else
    cachedLoop (step n)


end Collatz
