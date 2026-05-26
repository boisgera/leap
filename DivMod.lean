import Mathlib

-- TODO: make a "one-step reduction" and integrate in the def the proof of the
-- invariant? (Instead of splitting code and proof afterwards)

-- Returns divisor, remainder, quotient
def divModAux (b r q : ℕ) (h : b ≠ 0 := by grind) : ℕ × ℕ × ℕ :=
  if _ : r < b then
    (b, r, q) -- we could also return h for consistency...
  else
    divModAux b (r - b) (q + 1) h

#eval divModAux 5 17 0
-- (5, 2, 3)

def divMod (a b : ℕ) : ℕ × ℕ :=
  if h : b = 0 then
    (0, a)
  else
    let (_, r, q) := divModAux b a 0 h
    (q, r)

#eval divMod 17 5
-- (3, 5)

def div (a b : ℕ) : ℕ := (divMod a b).1

def mod (a b : ℕ) : ℕ := (divMod a b).2

-- Proof by induction
lemma divModAux_lt (b r q : ℕ) (h : b ≠ 0) : (divModAux b r q h).2.1 < b := by
  rw [divModAux]
  split_ifs with hr
  . simp only
    exact hr
  . exact divModAux_lt b (r - b) (q + 1) h

theorem remainder_lt (a b : ℕ) (h: b ≠ 0) : mod a b < b := by
  rw [mod, divMod]
  simp only [dif_neg h]
  exact divModAux_lt b a 0 h

-- Proof by induction
lemma divModAux_eq (b r q : ℕ) (h : b ≠ 0):
  b * (divModAux b r q h).2.2 + (divModAux b r q h).2.1 = b * q + r := by
  rw [divModAux]
  cases em (r < b) with
  | inl hl =>
    simp [hl]
  | inr hr =>
    simp [hr]
    have t := divModAux_eq b (r - b) (q + 1) h
    rw [t]
    grind

-- Note: since we have defined divMod a 0 to be (0, a),
-- we don't need to assume that b ≠ 0 here.
theorem divMod_eq (a b : ℕ) : b * (div a b) + (mod a b) = a := by
  rw [div, mod, divMod]
  cases em (b = 0) with
  | inl h =>
    simp [dif_pos h]
  | inr h =>
    simp [dif_neg h]
    have t := divModAux_eq b a 0 h
    rw [t]
    grind


-- TODO: proof that the remainder of a divMod with b = 2 is either
-- 0 or 1.
