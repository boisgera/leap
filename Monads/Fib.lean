import Mathlib

import Std
open Std.Time (Timestamp)

#print Std.Time.Second.Offset
#print Std.Rco

def main : IO Unit := do
  IO.print "Hello "
  IO.println "world!"
  -- let ts ← Timestamp.now
  -- IO.println s!"ts := {ts}"
  for i in 0...10 do
    IO.sleep 1000
    IO.println s!"Step {i} : {← Timestamp.now}"
    if i = 2 then
      break
  let mut sum := 0
  for i in Std.Rco.mk 0 10 do
    sum := sum + i * i
  IO.println sum

#eval main

-- Also: while (with mutation) and repeat (with break).

#eval (do
  let mut c := 0
  while c < 10 do
    IO.print "*"
    c := c + 1
  : IO Unit
)
-- **********

#eval (do
  let mut c := 0
  repeat
    IO.print "*"
    c := c + 1
    if c = 10 then break
  : IO Unit
)
-- **********

def fib (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10

#guard fib 10 = 55

def fib' (n : ℕ) (f0 := 0) (f1 := 1) : ℕ :=
  match n with
  | 0 => f0
  | 1 => f1
  | n + 2 => fib' (n + 1) f1 (f0 + f1)

#guard fib' 10 = 55


def IO.fib (n : ℕ) (f0 := 0) (f1 := 1) : IO ℕ := do
  if n = 0 then
    return f0
  else if n = 1 then
    return f1
  else
    let mut (a, b) := (f0, f1)
    for _ in 0...(n - 1) do
      (a, b) := (b, a + b)
    return b

#check IO.fib 10 -- IO ℕ

#eval IO.fib 10
-- 55

#print Id
-- @[implicit_reducible] def Id.{u} : Type u → Type u :=
-- fun type => type

def Id.fib (n : ℕ) (f0 := 0) (f1 := 1) : ℕ := Id.run do
  if n = 0 then
    return f0
  else if n = 1 then
    return f1
  else
    let mut (a, b) := (f0, f1)
    for _ in 0...(n - 1) do
      (a, b) := (b, a + b)
    return b

theorem OMG! : Id ℕ = ℕ := by rfl

#synth Monad Id -- yes!

def fib55 : ℕ := Id.fib 10

#eval fib55


def fibS (n : ℕ) (count := 0) : ℕ × ℕ :=
  let count' := count + 1
  match n with
  | 0 => (0, count')
  | 1 => (1, count')
  | n + 2 =>
    let (fn, count'') := fibS n count'
    let (fn1, count''') := fibS (n + 1) count''
    (fn + fn1, count''')

#eval fibS 10 -- (55, 177)

def fib'S (n : ℕ) (f0 := 0) (f1 := 1) (count := 0) : ℕ × ℕ :=
  let count' := count + 1
  match n with
  | 0 => (f0, count')
  | 1 => (f1, count')
  | n + 2 => fib'S (n + 1) f1 (f0 + f1) (count')

#eval fib'S 10 -- (55, 10)

#print StateM
-- @[reducible] def StateM.{u} : Type u → Type u → Type u :=
-- fun σ α => StateT σ Id α

#print StateT
-- @[implicit_reducible] def StateT.{u, v} : Type u → (Type u → Type v) → Type u → Type (max u v) :=
-- fun σ m α => σ → m (α × σ)

theorem OMG2 (α : Type) : StateM ℕ α = (ℕ → α × ℕ) := by rfl

abbrev CounterM := StateM ℕ

def StateM.fib (n : ℕ) : CounterM ℕ := fun count =>
  let count' := count + 1
  match n with
  | 0 => (0, count')
  | 1 => (1, count')
  | n + 2 =>
    let (fn, count'') := fib n count'
    let (fn1, count''') := fib (n + 1) count''
    (fn + fn1, count''')

#eval (StateM.fib 10) 0 -- (55, 177)
#eval (StateM.fib 10).run 0 -- (55, 177)
#eval (StateM.fib 10).run' 0 -- 55

def StateM.fib2 (n : ℕ) : CounterM ℕ := do
  let count ← fun c => (c, c) -- get the state
  let _ ←  fun _ => ((), count + 1)  -- set the new state
  match n with
  | 0 => return 0
  | 1 => return 1
  | n + 2 =>
    let fn ← fib2 n
    let fn1 ← fib2 (n + 1)
    return fn + fn1

#eval (StateM.fib2 10).run 0 -- (55, 177)

def StateM.fib3 (n : ℕ) : CounterM ℕ := do
  let count ← get ; set (count + 1) -- or instead, modify (· + 1)
  match n with
  | 0 => return 0
  | 1 => return 1
  | n + 2 => return (← fib3 n) + (← fib3 (n + 1))

#eval (StateM.fib3 10).run 0 -- (55, 177)

def Option.fib (n : ℕ) : Option ℕ :=
  match n with
  | 0 => some 0
  | 1 => some 1
  | n + 2 =>
    match fib n with
    | none => none
    | some fn =>
      match fib (n + 1) with
      | none => none
      | some fn1 =>
        let sum := fn + fn1
        if sum < 256 then
          some sum
        else
          none

#eval Option.fib 13 -- some 233
#eval Option.fib 14 -- none

def Option.fib2 (n : ℕ) : Option ℕ := do
  match n with
  | 0 => return 0
  | 1 => return 1
  | n + 2 =>
    let fn ← fib2 n
    let fn1 ← fib2 (n + 1)
    let sum := fn + fn1
    if sum < 256 then
      return sum
    else
      failure

#eval Option.fib2 13 -- some 233
#eval Option.fib2 14 -- none


abbrev CounterM' := StateT ℕ Option

def StateT.fib (n : ℕ) : CounterM' ℕ := do
  modify (· + 1)
  match n with
  | 0 => return 0
  | 1 => return 1
  | n + 2 =>
    let fn ← fib n
    let fn1 ← fib (n + 1)
    let sum := fn + fn1
    if sum < 256 then
      return sum
    else
      failure

#eval (StateT.fib 10).run 0
-- some (55, 177)
#eval (StateT.fib 13).run 0
-- some (233, 753)
#eval (StateT.fib 14).run 0
-- none
