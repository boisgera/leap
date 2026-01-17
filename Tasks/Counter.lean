import Std.Sync.Channel

structure Counter where
  count : Int
  c_add : IO (Std.Channel Int)


def Counter.new (count : Int := 0) : IO Counter :=
  let actor : Counter := {
    count := count,
    c_add := Std.Channel.new (α := Int)
  }
  /- Mmm we need to start the listening loop here! -/

  return actor

partial def counter (c : Std.Channel Int) (count : Int) : IO Unit := do
  let extra := (<- c.recv).get
  counter c (count + extra)

def main : IO Unit := do
  let c <- Std.Channel.new (α := Int) (capacity := none)
  let c := c.sync
  let t_counter <- IO.asTask (counter c 0)
  IO.println "counter"
