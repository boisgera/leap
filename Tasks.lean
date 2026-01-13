


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
