
-- Introduction to L∃∀N

#eval do IO.println (<- IO.FS.readFile "collatz.py")
-- import sys
--
-- def collatz(x0, n):
--     x = x0
--     for _ in range(n):
--         if x % 2 == 0:
--             x = x // 2
--         else:
--             x = 3 * x + 1
--     return x
--
-- if __name__ == "__main__":
--     args = [int(arg) for arg in sys.argv[1:]]
--     if len(args) == 2:
--        print(collatz(args[0], args[1]))
--     else:
--        print("Usage: python collatz.py <x0> <n>")

#eval IO.Process.run {
  cmd := "python",
  args := #["collatz.py", "42", "100"],
}
-- "2\n"

abbrev ℕ := Nat

def collatz_py (x₀ : ℕ) (n : ℕ) : IO ℕ := do
  let cmd := "python"
  let args := #["collatz.py", toString x₀, toString n]
  let output <- IO.Process.run { cmd, args }
  return String.toNat! output.trim

#eval collatz_py 42 10
-- 2

def collatz₀ (x₀ : ℕ) (n : ℕ) : ℕ := Id.run do
  let mut x <- x₀
  for _ in [0:n] do
    if x % 2 == 0 then
      x <- x / 2
    else
      x <- 3 * x + 1
  return x

#eval collatz₀ 42 10
-- 2

def collatz_step₀ (x₀ : ℕ) : ℕ := Id.run do
  if x₀ % 2 == 0 then
    return x₀ / 2
  else
    return 3 * x₀ + 1

def collatz_step₁ (x₀ : ℕ) : ℕ :=
  if x₀ % 2 == 0 then
    x₀ / 2
  else
    3 * x₀ + 1

def collatz_step := collatz_step₁

def collatz₁ (x₀ : ℕ) (n : ℕ) : ℕ := Id.run do
  let mut x <- x₀
  for _ in [0:n] do
    x <- collatz_step x
  return x

#eval collatz₁ 42 10
-- 2

def collatz₂ (x₀ : ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => x₀
  | n + 1 => collatz₂ (collatz_step x₀) n

def collatz₃ (x₀ : ℕ) : ℕ → ℕ
  | 0 => x₀
  | n + 1 => collatz₃ (collatz_step x₀) n

def collatz := collatz₃

def collatz_sequence (x₀ : ℕ) (n : ℕ) : List ℕ := Id.run do
    let mut x := x₀
    let mut xs := [x₀]
    for _ in [0:n] do
      x <- collatz_step x
      xs <- xs ++ [x]
    return xs

#eval collatz_sequence 42 10
-- [42, 21, 64, 32, 16, 8, 4, 2, 1, 4, 2]

def collatz_until_one₀ (x₀ : ℕ) : List ℕ := Id.run do
  let mut x := x₀
  let mut xs := [x₀]
  while x != 1 do
    x <- collatz_step x
    xs <- xs ++ [x]
  return xs

#eval collatz_until_one₀ 42
-- [42, 21, 64, 32, 16, 8, 4, 2, 1]

def collatz_until_one₁ (x₀ : ℕ) : List ℕ := Id.run do
  let mut x := x₀
  let mut xs := [x₀]
  while x != 1 do
    x <- collatz_step x
    xs <- x :: xs
  return xs.reverse

#eval collatz_until_one₁ 42
-- [42, 21, 64, 32, 16, 8, 4, 2, 1]

partial def collatz_until_one₂ (x₀ : ℕ) (xs : List ℕ := []) : List ℕ :=
  match xs with
  | [] => collatz_until_one₂ x₀ [x₀]
  | 1 :: _ => xs.reverse
  | x :: _ =>
    let x' := collatz_step x
    collatz_until_one₂ x' (x' :: xs)

#eval collatz_until_one₂ 42
-- [42, 21, 64, 32, 16, 8, 4, 2, 1]

theorem collatz_zero : ∀ (n : ℕ), collatz 0 n = 0 := by
  intro n
  induction n with
  | zero =>
    simp [collatz]
    simp [collatz₃]
  | succ n ih =>
    simp [collatz]
    simp [collatz₃]
    simp [collatz_step]
    simp [collatz_step₁]
    simp [collatz] at ih
    assumption

theorem collatz_conjecture :
  ∀ (x₀ : ℕ), x₀ > 0 -> ∃ (n : ℕ), collatz x₀ n = 1 := by
  admit
