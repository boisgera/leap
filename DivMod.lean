import Mathlib


namespace Sandbox

-- TODO: make a "one-step reduction" and integrate in the def the proof of the
-- invariant? (Instead of splitting code and proof afterwards)?

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

theorem mod_lt (a b : ℕ) (h : b ≠ 0) : mod a b < b := by
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
theorem mul_div_add_mod (a b : ℕ) : b * (div a b) + (mod a b) = a := by
  rw [div, mod, divMod]
  cases em (b = 0) with
  | inl h =>
    simp [dif_pos h]
  | inr h =>
    simp [dif_neg h]
    have t := divModAux_eq b a 0 h
    rw [t]
    grind

-- TODO: define "divides"? Yes

def divides (b a : ℕ) : Prop := mod a b = 0

-- TODO: this is decidable, use it? We'll make dite and dif conditions out of
-- this...

theorem div_mod (a b q r : ℕ) (h_lt : r < b) (h_eq : b * q + r = a) :
    (q = div a b) ∧ (r = mod a b) := by
  -- TODO: show that b ≠ 0
  -- TODO: show that q' = div a b and r' = mod a b satisfy the assumptions.
  -- TODO: get b * q + r = b * q' + r'
  -- TODO: embed this stuff into ℤ to conclude based divisibility by b? Urk.
  -- Find the sign of stuff, then rw as b * (q - q') = r' - r and apply some
  -- divmod to both sides?
  admit

def Even (n : ℕ) : Prop := mod n 2 = 0
def Odd (n : ℕ) : Prop := mod n 2 = 1

-- TODO: alt version with `2 * k` or `2 * k + 1` shape.

theorem even_or_odd (n : ℕ) : Even n ∨ Odd n := by
  rw [Even, Odd]
  have := mod_lt n 2 (show 2 ≠ 0 from by norm_num)
  grind



end Sandbox
