import Mathlib

-- Demonstration of classic use of definition by recursion and
-- proof by induction and their low-level counterpart using Nat.rec.

-- ⚠️ Warning: with this convention the partial sum starts at 0; a 0 comes next.
--  But OTOH, the definition of the reciprocal (diff) is more natural.
def psum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

-- We could/should also define psum by recursion and show that it's the same.

def diff (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1) - a n

#check Finset.sum_insert

theorem diff_of_sum_eq_id (a : ℕ → ℝ) : diff (psum a) = a := by
  ext n
  simp only [psum, diff]
  simp only [Finset.sum_range_succ]
  simp only [add_sub_cancel_left]

-- The sequence 0, 1, 2, 3, etc. (as real values), defined by recursion.
def natCast (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => (natCast) n + 1

theorem natCast_eq : natCast = Nat.cast := by
  ext n
  induction n with
  | zero =>
    rw [natCast]
    rw [Nat.cast_zero]
  | succ n ih =>
    rw [natCast]
    rw [Nat.cast_add, Nat.cast_one]
    rw [ih]

example : ∀ n, (psum natCast) n = n * (n - 1) / 2 := by
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    norm_num
    rw [psum, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [psum] at *
    rw [Finset.sum_range_succ]
    rw [ih]
    rw [natCast_eq]
    -- ⊢ ↑n * (↑n - 1) / 2 + ↑n = ↑(n + 1) * (↑(n + 1) - 1) / 2
    -- at this stage, grind would work.
    simp only [Nat.cast_add, Nat.cast_one]
    -- ↑n * (↑n - 1) / 2 + ↑n = (↑n + 1) * (↑n + 1 - 1) / 2
    field_simp
    ring

#check Nat.rec -- The full dependent recursor (needed for the proofs;
-- for the construction of mathematical objects, constant motives are enough)
-- Nat.rec.{u} {motive : ℕ → Sort u}
-- (zero : motive Nat.zero) (succ : (n : ℕ) → motive n → motive n.succ) (t : ℕ) :
-- motive t

def psum' (a : ℕ → ℝ) : ℕ → ℝ :=
  let motive : ℕ → Type := fun _ => ℝ -- constant type-valued motive
  Nat.rec (motive := motive) 0 (fun n sum_n => sum_n + a n)

def natCast' := psum' (fun _ => 1) -- to get the ramp, add ones.

theorem natCast'_eq : natCast' = Nat.cast := by
  let motive (n : ℕ) : Prop := natCast' n = Nat.cast n -- not constant!
  let p := Nat.rec
    (motive := motive)
    (show
        natCast' 0 = Nat.cast 0 from by
      rw [Nat.cast_zero]
      rw [natCast', psum'] -- Nat.rec 0 (fun n sum_n => sum_n + 1) 0 = 0
      rw [Nat.rec_zero]
    )
    (show
        ∀ (n : ℕ),
        natCast' n = Nat.cast n →
        natCast' (n + 1) = Nat.cast (n + 1) from by
      intro n ih
      rw [natCast', psum']
      -- ⊢ Nat.rec 0 (fun n sum_n => sum_n + 1) (n + 1) = ↑(n + 1)
      rw [Nat.cast_add, Nat.cast_one]
      simp only -- applies Nat.rec_add_one automatically !?!
      rw [natCast', psum'] at ih
      rw [ih]
    )
  ext n
  exact p n
