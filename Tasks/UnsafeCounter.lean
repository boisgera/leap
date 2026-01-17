import Std.Sync.Channel

def UnsafeCounter := IO.Ref Int -- exposes get, set, modify, take, ...

namespace UnsafeCounter

def new (n : Int) : IO UnsafeCounter :=
  IO.mkRef n

def add (counter : UnsafeCounter) (n : Int) : IO Unit := do
  let count <- counter.get
  counter.set (count + n)

unsafe def safe_add (counter : UnsafeCounter) (n : Int) : IO Unit := do
  let count <- counter.take
  counter.set (count + n)

end UnsafeCounter

unsafe def main : IO Unit := do
  let counter <- UnsafeCounter.new 0

  IO.println "Unsafe and ugly"
  for epoch in [0:10] do
    for _ in [0:1000] do
      counter.add ( 1) |> IO.asTask |> discard
      counter.add (-1) |> IO.asTask |> discard
    IO.sleep 1_000 -- wait for the dust to settle
    IO.println s!"step {epoch}, count: {<- counter.get}"
  IO.println ""

  -- The same issue but now we wait less and we are sure that all the tasks
  -- are actually done.
  IO.println "Still unsafe but cleaner"
  counter.set 0
  let mut tasks : List (Task (Except IO.Error Unit)) := []
  for epoch in [0:10] do
    for _ in [0:1000] do
      tasks := (<- IO.asTask <| counter.add ( 1)) :: tasks
      tasks := (<- IO.asTask <| counter.add (-1)) :: tasks
    _ := tasks.map (fun task => task.get) -- wait for completion
    tasks := []
    IO.println s!"step {epoch}, count: {<- counter.get}"
  IO.println ""

  IO.println "'Safe' (but marked as unsafe...)"
  counter.set 0
  for epoch in [0:10] do
    for _ in [0:1000] do
      tasks := (<- IO.asTask <| counter.safe_add ( 1)) :: tasks
      tasks := (<- IO.asTask <| counter.safe_add (-1)) :: tasks
    _ := tasks.map (fun task => task.get) -- wait for completion
    tasks := []
    IO.println s!"step {epoch}, count: {<- counter.get}"
  IO.println ""


  -- The safe version.
  IO.println "Safe and clean"
  counter.set 0
  for epoch in [0:10] do
    for _ in [0:1000] do
      tasks := (<- IO.asTask <| counter.modify (· + 1)) :: tasks
      tasks := (<- IO.asTask <| counter.modify (· - 1)) :: tasks
    _ := tasks.map (fun task => task.get) -- wait for completion
    tasks := []
    IO.println s!"step {epoch}, count: {<- counter.get}"
  IO.println ""
