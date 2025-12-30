import Mathlib

def seq_lim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ m, ∀ n ≥ m, |a n - ℓ| < ε

def converges (a : ℕ → ℝ) := ∃ ℓ, seq_lim a ℓ

def is_cauchy (a : ℕ → ℝ) := ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ p ≥ m, |a n - a p| < ε

theorem converges_of_is_cauchy {a : ℕ → ℝ} : converges a -> is_cauchy a := by
  simp_rw [converges, seq_lim, is_cauchy]
  intro ⟨ℓ, hℓ⟩ ε ε_pos
  specialize hℓ (ε / 2) (show ε / 2 > 0 by linarith)
  let ⟨m, hm⟩ := hℓ
  use m
  intro n n_ge_m p p_ge_m
  let hn := hm n n_ge_m
  let hp := hm p p_ge_m
  calc |a n - a p|
    _ = |(a n - ℓ) - (a p - ℓ)| := by ring_nf
    _ ≤ |a n - ℓ| + |a p - ℓ| := by apply abs_sub
    _ < ε := by linarith

theorem sum_of_cauchy {a b : ℕ → ℝ} :
    is_cauchy a -> is_cauchy b -> is_cauchy (a + b) := by
  simp only [is_cauchy]
  intro ha hb ε ε_pos
  specialize ha (ε / 2) (by linarith)
  specialize hb (ε / 2) (by linarith)
  obtain ⟨ma, ha⟩ := ha
  obtain ⟨mb, hb⟩ := hb
  let m := max ma mb
  use m
  intro n n_ge_m p p_ge_m
  simp only [Pi.add_apply]
  specialize ha n (by grind) p (by grind)
  specialize hb n (by grind) p (by grind)
  calc |a n + b n - (a p + b p)|
    _ = |(a n - a p) + (b n - b p)| := by ring_nf
    _ ≤ |a n - a p| + |b n - b p|   := by apply abs_add_le
    _ < ε                           := by linarith

def is_bounded (a : ℕ → ℝ) := ∃ x, ∀ n, |a n| ≤ x

#print Finset.sup
-- def Finset.sup.{u_2, u_3} : {α : Type u_2} → {β : Type u_3} →
--    [inst : SemilatticeSup α] → [OrderBot α] → Finset β → (β → α) → α :=
--   fun {α} {β} [SemilatticeSup α] [OrderBot α] s f => Finset.fold (fun x1 x2 => x1 ⊔ x2) ⊥ f s

#check Finset.range
-- Finset.range (n : ℕ) : Finset ℕ

#check Finset.le_max'
-- Finset.le_max'.{u_2} {α : Type u_2} [LinearOrder α]
--     (s : Finset α) (x : α) (H2 : x ∈ s) : x ≤ s.max' ⋯

theorem bounded_of_cauchy {a : ℕ → ℝ} : is_cauchy a → is_bounded a := by
  have aux (m : ℕ) : ∀ m, ∃ b, ∀ n ≤ m, |a n| ≤ b := by
    intro m
    let vals := m + 1 |> Finset.range |>.image (|a ·|)
    let b := if h : vals.Nonempty then
      vals.max' h
    else
      0
    use b
    intro n n_le_m
    have abs_a_n_in_vals : |a n| ∈ vals := by admit
    by_cases h' : vals.Nonempty --- Mmm type coercion issue now?
    . exact vals.le_max' (x := |a n|) (H2 := abs_a_n_in_vals)
    . grind
  admit
