import Lake

def pmap {α β} (f : α → β) (inputs : List α) : List β :=
  -- let t_inputs : List (Task α) := inputs.map Task.pure
  -- let t_inputs := inputs.map fun input => Task.spawn (fun () => input)
  -- let t_outputs := t_inputs.map (fun t_input => t_input.map f)
  -- t_outputs.map Task.get
  let t_outputs := inputs.map (fun input => Task.spawn fun _ => f input)
  t_outputs.map Task.get

def countdown (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => countdown n

def test : IO Unit := do
  IO.println "pmap test"
  let n := 10_000_000_000
  let inputs := [n, 2 * n, 3 * n, 4 * n, 5 * n, 6 * n, 7 * n, 8 * n]
  inputs |> pmap countdown |> IO.println

def test_baseline : IO Unit := do
  IO.println "Hello!"
  -- let n := 10_000_000_000
  -- let inputs := [n, 2 * n, 3 * n, 4 * n, 5 * n, 6 * n, 7 * n, 8 * n]
  -- let tasks := inputs.map fun input => (Task.spawn fun () => countdown input)
  -- let outputs := tasks.map Task.get
  -- IO.println outputs

def main := test_baseline -- neither version of pmap works as (I was) expecting.
-- I probably need to understand more about what's going on when a task is
-- done (is the thread relinquished?) and what map is doing when I starts
-- on a task that is already done.

-- def main := main_baseline -- This one heats the room as expected.

-- def main := IO.println "test"
