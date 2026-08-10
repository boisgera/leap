
def List.parMap {α β} (f : α → β) (l : List α) : List β :=
  let tasks := l.map (fun x => Task.spawn (fun _ => f x))
  tasks.map (fun task => task.get)

def main : IO Unit := do
  let result : List Nat <- timeit
    "sequential map"
    do
      return 8 |> List.range |>.map (. ^ 2)
  IO.println result
  let result : List Nat <- timeit
    "parallel map"
    do
      return 8 |> List.range |>.parMap (. ^ 2)
  IO.println result
