import Mathlib

theorem even_of_square_even (n : ℕ) : Even (n * n) -> Even n := by
  contrapose
  repeat rw [Nat.not_even_iff_odd]
  intro ⟨k, odd_n⟩
  let m := 2 * k * k + 2 * k
  exact ⟨m, show n * n = 2 * m + 1 by grind⟩

-- Rk: the difference of even numbers is even is a standard result for n ∈ ℤ.
-- Thus we derive the theorem for relative numbers first and use the known
-- result that Even (n : ℕ) <-> Even (↑n : ℤ)
theorem even_of_square_even_int (n : ℤ) : Even (n * n) -> Even n := by
  intro square_even
  let m := n * (n + 1) - n * n
  have n_eq_m : n = n * (n + 1) - n * n := by grind
  have even_m: Even (n * (n + 1) - n * n) :=
    Even.sub (Int.even_mul_succ_self n) square_even
  rw [<- n_eq_m] at even_m
  exact even_m

theorem even_of_square' (n : ℕ) : Even (n * n) -> Even n := by
  intro square_even
  have square_even_int : Even (↑n * ↑n : ℤ) := by
    have : (↑(n * n) : ℤ)  = ↑n * ↑n := Int.cast_mul n n
    rw [<- this]
    exact (Int.even_coe_nat (n * n)).mpr square_even
  have even_int := (even_of_square_even_int n) square_even_int
  exact (Int.even_coe_nat n).mp even_int
