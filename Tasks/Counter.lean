import Std.Sync.Channel

partial def counter (c : Std.Channel Int) (count : Int) : IO Unit := do
  let extra := (<- c.recv).get
  counter c (count + extra)

def main : IO Unit := do
  let c <- Std.Channel.new (α := Int) (capacity := none)
  let c := c.sync
  let t_counter <- IO.asTask (counter c 0)
  IO.println "counter"
