
def List.parMap {α β} (f : α → β) (l : List α) : List β :=
  let tasks := l.map (fun x => Task.spawn (fun _ => f x))
  tasks.map (fun task => task.get)

partial def collatz (n start : Nat) : Nat :=
  if n == 0 then
    start
  else if start % 2 == 0 then
    collatz (n - 1) (start / 2)
  else
    collatz (n - 1) (3 * start + 1)

def main : IO Unit := do
  let n := 100_000_000
  let result : List Nat <- timeit
    "sequential map"
    do
      return 8 |> List.range |>.map (collatz n)
  IO.println result
  let result : List Nat <- timeit
    "parallel map"
    do
      return 8 |> List.range |>.parMap (collatz n)
  IO.println result
