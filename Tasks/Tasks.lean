import Mathlib
import Lake.Util.Task -- Now `Task` is a `Monad`

/-!
-/

set_option pp.showLetValues true

/-!
# Tasks
-/

/-!
## Pure Tasks
-/

#check List.max

abbrev NonemptyList α := {l : List α // l ≠ []}

def List.split {α} (l : List α) (h : l.length > 2) : NonemptyList α × NonemptyList α :=
  let n := l.length / 2
  let l_1 := l.take n
  have l_1_nonempty : l_1 ≠ [] := by
    apply List.length_pos_iff.mp
    rw [List.length_take]
    omega
  let l_2 := l.drop n
  have l_2_nonempty : l_2 ≠ [] := by
    apply List.length_pos_iff.mp
    rw [List.length_drop]
    omega
  (⟨l_1, l_1_nonempty⟩, ⟨l_2, l_2_nonempty⟩)


def parallel_max {α} [Max α] (l : List α) (h : l.length > 2 := by grind) : α :=
  let (l_1, l_2) := List.split l h
  let task_1 := Task.spawn fun () => List.max l_1.val l_1.property
  let task_2 := Task.spawn fun () => List.max l_2.val l_2.property
  let max_1 := task_1.get
  let max_2 := task_2.get
  max max_1 max_2

#eval parallel_max [1, 2, 3, 4, 5, 6]

/-!
The stuff above is fun but if we want to focus on the task stuff and not the
proof stuff, it's probably better to focus on some operation that has a
default value for max of the empty list.
-/

def List.maxWithBot{α} [LinearOrder α] [OrderBot α] (l : List α) : α :=
  match l with
  | [] => ⊥
  | [a] => a
  | a :: as => max a as.maxWithBot

#eval ([] : List Nat).maxWithBot
-- 0
#eval [2, 1].maxWithBot
-- 2
#eval [0, 1, 2, 7, 89, 5, 23].maxWithBot
-- 89

def pmax {α} [LinearOrder α] [OrderBot α] (l : List α) : α :=
  let n := l.length / 2
  let (l_1, l_2) := (l.take n, l.drop n)
  let task_1 := Task.spawn fun () => l_1.maxWithBot
  let task_2 := Task.spawn fun () => l_2.maxWithBot
  max task_1.get task_2.get

def pmax' {α} [LinearOrder α] [OrderBot α] (l : List α) : α :=
  let n := l.length / 2
  let (l_1, l_2) := (l.take n, l.drop n)
  let task_1 := Task.spawn fun () => l_1.maxWithBot
  let task_2 := Task.spawn fun () => l_2.maxWithBot
  [task_1, task_2] |> Task.mapList List.maxWithBot |>.get


/-!
Nota: the API is a bit weird above; what's I'd like to do is
"compute this function with this argument in a thread". And I think that
we can do that with pure and bind (see monadic structure). And then after
we gather the result.
-/

def sumOfSquares (numbers : List ℕ) : ℕ :=
  numbers |>.map (· ^ 2) |>.sum

#eval sumOfSquares [1, 2, 3]
-- 14

#check Task.map
-- Task.map.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) (x : Task α)
--   (prio : Task.Priority := Task.Priority.default) (sync : Bool := false) : Task β

/-!
WARNING: this is WRONG. pure then map on Tasks spawns nothing AFAICT.
Or does it? Arf unclear to me...
-/

/--
Compute the squares in separate tasks
-/
def sumOfSquares' (numbers : List ℕ) : ℕ :=
  -- seed the tasks with already known numbers (no computation so far)
  let t_numbers : List (Task ℕ) := numbers.map Task.pure
  -- square them
  let t_squares : List (Task ℕ) := t_numbers.map (
    fun (task : Task ℕ) => task.map (· ^ 2)
  )
  -- fetch the results and sum them
  let squares : List ℕ := t_squares.map Task.get
  squares.sum

#eval sumOfSquares' [1, 2, 3]
-- 14

/--
Alt version using the monadic structure of lists (of tasks)
-/
def sumOfSquares'' (numbers : List ℕ) : ℕ :=
  let t_squares : List (Task ℕ) := do
    let number <- numbers
    let square := number |> Task.pure |>.map (· ^ 2)
    return square
  let squares : List ℕ := t_squares.map Task.get
  squares.sum

#eval sumOfSquares'' [1, 2, 3]
-- 14

/-!
⚠️ We need to import Lake to have `Task` declared as a `Monad`.
-/
#check (inferInstance : Monad Task)

/-
We can also use the `do` and `return` notation for tasks.
-/

def sumOfSquares_3 (numbers : List ℕ) : ℕ :=
  let t_squares : List (Task ℕ) := do
    let number <- numbers
    let square : Task ℕ := do
      return number ^ 2
    return square
  let squares : List ℕ := do
    let t_square <- t_squares
    return t_square.get
  squares.sum

#eval sumOfSquares_3 [1, 2, 3]
-- 14

/-!
⛳ Code golf version (not worth it!!!)
-/

def sumOfSquares_4 (numbers : List ℕ) : ℕ :=
  let t_squares : List (Task ℕ) := do
    let number <- numbers
    return (return number ^ 2 : Task ℕ)
  (return (<- t_squares).get) |>.sum

#eval sumOfSquares_4 [1, 2, 3]
-- 14

/-!
Let's abstract a bit a parallel map and use it to achieve the same result.
-/

def pmap_wrong {α β} (f : α → β) (inputs : List α) : List β := do
  let input <- inputs
  let t_output : Task β := return f input
  let output := t_output.get
  return output

#eval [1, 2, 3] |> pmap_wrong (· ^ 2) |>.sum
-- 14

/-!
📌 : use a large computation as f and check that several threads are used.
Claude code tells me that it's invalid since the the `pmap` is equivalent to:
```
inputs.map (fun input =>
  let t_output := Task.pure (f input)
  t_output.get)
```

That makes sense. I need to generate the tasks in one do block and wait for
the results in another one.
-/

/-
Let's do the correct version. Actually, the do notation for lists is rather
detrimental here IMHO (and actually it's only defined by Mathlib, not Lean
itself!), let's use pure and map & stuff...

Let's put that in the `List` namespace and call is `tmap` (`t` for `Task`,
since `List.pmap` is already taken.)
-/

def List.tmap {α β} (f : α → β) (inputs : List α) : List β :=
  let t_inputs : List (Task α) := inputs.map Task.pure
  let t_outputs := t_inputs.map (fun t_input => t_input.map f)
  t_outputs.map Task.get

#eval [1, 2, 3] |>.tmap (· ^ 2) |>.sum
-- 14

/-
A variant which uses:

  - pipes to chain operation on lists,

  - the monadic structure of `Task`
    (defined by the `Lake` module, not available out of the box).
-/


def List.tmap' {α β} (f : α → β) (inputs : List α) : List β :=
  inputs
    |>.map (fun input : α => return input)
    |>.map (fun t_input => return f (<- t_input))
    |>.map Task.get

/-!
With this we can for example do
-/

def countdown (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => countdown n

def parallel_countdown: IO Unit := do
  let n := 1_000_000
  let inputs := 8 |> List.range |>.map (· + 1) |>.map (· * n)
  IO.println s!"countdown inputs: {inputs}"
  let outputs := inputs.tmap countdown
  IO.println s!"countdown outputs: {outputs}"

#eval parallel_countdown
-- countdown inputs: [1000000, 2000000, 3000000, 4000000, 5000000, 6000000, 7000000, 8000000]
-- countdown outputs: [0, 0, 0, 0, 0, 0, 0, 0]
/-!

/-
🚧 TODO: general map-reduce algo? I have to understand what shuffle is before that!
-/



## Impure Tasks
-/

def action : IO Unit := do
  IO.println "Hello!"
  discard <| IO.asTask do
    IO.println "in the background"
    IO.sleep 1000
    IO.println "in the background"
  let task <- IO.asTask do
    IO.sleep 1000
    return 42
  match task.get with
  | Except.ok value => IO.println value
  | Except.error _ => panic! "Ooops"
  IO.sleep 1000
  IO.println "Hello!"
  -- let task <- IO.asTask (IO.println "Hello world!")
  -- _ = task.get
  -- match task.get with
  -- | .ok _ => IO.println "ok."
  -- | .error _ => IO.println "error."

-- #check action
-- action : IO Unit

def main := action

/-!
### Blinking LEDs
-/

def displayWhite : IO Unit := do
  repeat
    IO.println "⚪"
    IO.sleep 1000

def displayBlack : IO Unit := do
  repeat
    IO.println "⚫"
    IO.sleep 500

def displayWhiteAndBlack : IO Unit := do
  let _t_display_white <- IO.asTask displayWhite
  let _t_display_black <- IO.asTask displayBlack
  IO.sleep 3_000

#eval 1+1
