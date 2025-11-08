import Mathlib

theorem even_of_square_even (n : ℕ) : Even (n * n) -> Even n := by
  contrapose
  repeat rw [Nat.not_even_iff_odd]
  intro ⟨k, odd_n⟩
  let m := 2 * k * k + 2 * k
  exact ⟨m, show n * n = 2 * m + 1 by grind⟩

namespace NotACoward

-- TODO: split parity logic and ℤ <-> ℕ conversion stuff.

theorem even_of_square (n : ℕ) : Even (n * n) -> Even n := by
  intro square_even
  have square_even_int : Even ((n : ℤ) * n) := by
    have : (↑(n * n) : ℤ) = (n : ℤ) * (n : ℤ) := Int.cast_mul n n
    rw [<- this]
    exact (Int.even_coe_nat (n * n)).mpr square_even
  have h₂ : (n : ℤ) = n * (n + 1) - n * n := by grind
  have h₃ : Even ((n : ℤ) * (n + 1)) := Int.even_mul_succ_self n
  have h₄ : Even ((n : ℤ) * (n + 1) - n * n) :=
    Even.sub h₃ square_even_int
  rw [<- h₂] at h₄
  exact (Int.even_coe_nat n).mp h₄

end NotACoward
