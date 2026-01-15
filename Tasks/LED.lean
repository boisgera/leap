def LED (symbol : String) (ms : UInt32 := 1000) : IO Unit := do
  repeat
    IO.println symbol
    IO.sleep ms

inductive TrafficLight where
| green
| orange
| red

def TrafficLight.symbol (tf : TrafficLight) : String :=
  match tf with
  | green => "🟢"
  | orange => "🟠"
  | red => "🔴"

def TrafficLight.rotate (tf : TrafficLight) : TrafficLight :=
  match tf with
  | green => orange
  | orange => red
  | red => green

-- The function can also call itself recursively to avoid using a repeat loop.
partial def trafficLight (tf : TrafficLight) (ms : UInt32 := 1000) : IO Unit := do
  IO.println tf.symbol
  IO.sleep 1000
  trafficLight tf.rotate ms

def main : IO Unit := do
  -- Here what matters is that the tasks start;
  -- the task objects themselves can be discarded.
  let _ <- IO.asTask (LED "⚪") -- or: discard (IO.asTask (LED "⚪"))
  let _ <- IO.asTask (LED "⚫" (ms := 500))
  let _ <- IO.asTask (trafficLight .green)
  -- The program doesn't stop until all threads are done.
