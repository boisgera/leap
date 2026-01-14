import Mathlib

set_option pp.showLetValues true

/-!
# Tasks
-/

/-!
## Pure Tasks
-/

#check List.max

-- TODO: externalize the list splitting (and the associated properties)

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

-- def task_1 := Task.spawn fun () => 1 + 1

-- #eval task_1.get
-- -- 2

-- -- def IO_task := IO.asTask (IO.println "Hello world!")
-- -- #check IO_task
-- -- task_2: BaseIO (Task (Except IO.Error Unit))

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
