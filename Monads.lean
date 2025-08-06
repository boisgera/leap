

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


def one_plus_one_python : IO String := do
  let spawnArgs := { cmd := "python3", args := #["-c", "print(1+1)"] }
  let out ←  IO.Process.run spawnArgs
  return out

def one_plus_one : IO Unit := do
  let result ← IO.Process.run { cmd := "python3", args := #["-c", "print(1+1)"] }
  IO.println s!"1 + 1 = {result}"

#eval one_plus_one
-- 1 + 1 = 2
