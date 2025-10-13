import Mathlib

#check String.leftpad
-- String.leftpad (n : ℕ) (c : Char := ' ') (s : String) : String

#print String.leftpad -- implemented using List of Char stuff. Great!
-- def String.leftpad : ℕ → optParam Char ' ' → String → String :=
-- fun n c s => { data := List.leftpad n c s.data }

#eval "Hello!".leftpad 10 '·'
-- "····Hello!"

theorem leftpad_prefix : -- <+: : isPrefix
  ∀ (n : Nat) (c : Char) (s : String),
  (List.replicate n c) <+: (s.leftpad (n + s.length) c).toList := by
  intro n c s
  rw [String.toList]
  rw [String.leftpad]
  rw [String.data]
  simp only
  rw [List.leftpad]
  rw [String.length]
  simp only
  simp only [Nat.add_sub_cancel]
  generalize (List.replicate n c) = t
  generalize s.data = r
  clear n c s -- t r : List Char ⊢ t <+: t ++ r
  rw [List.IsPrefix]
  use r
