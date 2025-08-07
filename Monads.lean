
abbrev ℕ := Nat

def randRange₀ (n : Nat) : Nat :=
  sorry

theorem reflexivity : ∀ (r : ℕ), r = r := by
  intro r
  rfl

theorem rand_theorem (n : Nat) : randRange₀ n = randRange₀ n :=
  reflexivity (randRange₀ n)

-- So .... we are only going to be able to have constant random numbers with
-- this signature !!!

def randRange (n : Nat) : IO Nat :=
  IO.Process.run {
    cmd := "python",
    args := #[
      "-c",
      s!"import random; print(random.randrange(0, {n}), end='')"
    ]
  } >>= (· |> String.toNat! |> pure)


#eval "0x" ++ String.mk (Nat.toDigits 16 255)

def hex₀ (n : Nat) : String :=
  "0x" ++ String.mk (Nat.toDigits 16 n)

def hex₁ (n : Nat) : String :=
  n |> fun n => Nat.toDigits 16 n |> String.mk |> fun s => "0x" ++ s

#eval hex₁ 42
-- "0x2a"

def hex₂ (n : Nat) : String :=
  n |> Nat.toDigits 16 |> String.mk |> ("0x" ++ ·)

def hex := hex₁


#eval hex 0
-- "0x0"

#eval hex 42
-- "0x2a"

#eval hex 255
-- "0xff"

#eval hex 4096
-- "0x1000"

def a := {
  cmd := "python3", args := #["-c"]
  : IO.Process.SpawnArgs
}

def strip_python (s : String) : IO String :=
  let python_code := s!"print('{s}'.strip(), end='')"
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := "python", args := #["-c", python_code]
  }
  IO.Process.run spawnArgs

#eval strip_python "  Hello world!  "
-- "Hello world!"

#eval strip_python "0x42\n"
-- process 'python' exited with code 1 !

def hex_python₀ (n : Nat) : IO String :=
  let python_code := s!"print(hex({n}))"
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := "python", args := #["-c", python_code]
  }
  IO.Process.run spawnArgs >>= strip_python

#eval hex_python₀
-- "0x2a"

def hex_python₉  (n : Nat) : IO String := do
  let python_code := s!"print(hex({n}))"
  let spawnArgs := { cmd := "python3", args := #["-c", python_code] }
  let out ← IO.Process.run spawnArgs
  return out.trim

#eval hex_python 42

def one_plus_one_python : IO String := do
  let spawnArgs := { cmd := "python3", args := #["-c", "print(1+1)"] }
  let out ←  IO.Process.run spawnArgs
  return out

def one_plus_one : IO Unit := do
  let result ← IO.Process.run { cmd := "python3", args := #["-c", "print(1+1)"] }
  IO.println s!"1 + 1 = {result}"

#eval one_plus_one
-- 1 + 1 = 2
