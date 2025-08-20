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

def exec! (code : String) : IO Unit := do
  let _ <- exec_output! code
  return ()

def eval! (code : String) : IO String := do
  exec_output! s!"_ = {code}; print(_, end='', flush=True)"

end Python
