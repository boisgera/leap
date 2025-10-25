import Mathlib

-- Tactics vs Manual Proofs, an example: show that every natural number is zero or a successor

#check Nat.rec
-- Nat.rec.{u} {motive : ℕ → Sort u}
-- (zero : motive Nat.zero)
-- (succ : (n : ℕ) → motive n → motive n.succ)
-- (t : ℕ) :
-- motive t

theorem v1 : ∀ n : Nat, n = 0 ∨ ∃ m : Nat, n = m + 1 :=
  Nat.rec
    (Or.inl (Eq.refl 0))
    fun p _ =>
      Or.inr (Exists.intro p (Eq.refl p.succ))

theorem v2 : ∀ n : Nat, n = 0 ∨  ∃ m : Nat, n = m + 1 := by
  apply Nat.rec
  . left
    rfl
  . intro m _
    right
    use m

#print v2
-- theorem v2 : ∀ (n : ℕ), n = 0 ∨ ∃ m, n = m + 1 :=
-- Nat.rec (Or.inl (Eq.refl Nat.zero)) fun m n_ih => Or.inr (Exists.intro m (Eq.refl m.succ))
