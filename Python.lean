/-
Spin a toupie server before any call to this library:

  uvx --from git+https://github.com/boisgera/toupie toupie

See https://github.com/boisgera/toupie for more information.
-/

namespace Python

def exec_output! (code : String) : IO String := do
  let out <- (IO.Process.output
    {
      cmd := "curl",
      args := #[
        "-X", "POST", "http://127.0.0.1:8000",
        "-H", "Content-Type: plain/text",
        "--data-binary", "@-",
      ],
      cwd := none,
      env := #[],
      inheritEnv := true,
    }
    (some code)
  )
  if out.exitCode != 0 then
    panic! s!"Command failed with exit code {out.exitCode}: {out.stderr}"
  return out.stdout

-- IO execution at the global level, see:
-- https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/
initialize shouldBatch : IO.Ref Bool <- IO.mkRef false
initialize todos : IO.Ref (List String) <- IO.mkRef []

def flush! : IO Unit := do
  let codes <- todos.get
  if not codes.isEmpty then
    let code := "\n".intercalate codes
    todos.set []
    discard (exec_output! code)

def batch {α} (action : IO α) : IO α := do
  shouldBatch.set true
  let result <- action
  flush!
  return result

def exec! (code : String) : IO Unit := do
  if (<- shouldBatch.get) then
    todos.modify (. ++ [code])
  else
    flush!
    discard (exec_output! code)

def eval! (code : String) : IO String := do
  flush!
  exec_output! s!"_ = {code}; print(_, end='', flush=True)"

end Python
