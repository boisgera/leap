import Std.Sync.Channel

/-!
The fact that [`Task.get` temporarily growth the thread pool][ref]
prevents (some) classic deadlock that could happen with channels and
fixed-size thread pools.

[ref]: https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/#Task___get
-/

abbrev Trigger := Std.Channel Unit

def link (input output : Trigger) : IO Unit := do
  _ ← input.sync.recv
  _ ← output.send ()

def done (trigger : Trigger) : IO Unit := do
  _ ← trigger.sync.recv
  IO.println "Done."

def newTrigger : IO (Trigger) :=
  Std.Channel.new (α := Unit) (capacity := some 0)

def spawn (action : IO Unit) : IO Unit := do
  _ <- IO.asTask action

-- This version is equivalent to n := 1 below
def main1 : IO Unit := do
  let t1 ← newTrigger
  let t2 ← newTrigger
  done t2 |> spawn
  link (input := t1) (output := t2) |> spawn
  IO.sleep 3000
  _ <- t1.send ()

def main : IO Unit := do
  let n := 32 -- pick anything larger than the thread pool
  let mut t <- newTrigger
  done t |> spawn -- start by end of the trigger chain
  for i in [0:n] do
    IO.println i
    let t_input ← newTrigger
    -- build and start the trigger chain upwards
    link (input := t_input) (output := t) |> spawn
    t := t_input
  IO.sleep 3000
  _ <- t.send ()
