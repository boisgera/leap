import Mathlib

-- Demonstration of classic use of definition by recursion and
-- proof by induction and their low-level counterpart using Nat.rec.

-- ⚠️ Warning: with our convention the partial sum starts at 0; a 0 comes next.
--  But OTOH, the definition of the reciprocal (diff) is more natural.
def psum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => (psum a n) + a n

theorem psum_eq_sum_range (a : ℕ → ℝ) (n : ℕ) :
    psum a n = ∑ i ∈ Finset.range n, a i := by
  induction n with
  | zero =>
    rw [psum]
    rw [Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [psum]
    rw [Finset.sum_range_succ]
    rw [ih]

def diff (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1) - a n

theorem diff_of_psum : diff ∘ psum  = id := by
  ext a n
  rw [Function.comp_apply]
  rw [id] -- ⊢ diff (psum a) n = a n
  induction n with
  | zero =>
    rw [diff]
    simp only [psum]
    ring
  | succ n ih =>
    rw [diff]
    repeat rw [psum]
    ring

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
    rw [psum]
    norm_num
  | succ n ih =>
    rw [psum]
    nth_rewrite 2 [natCast_eq]
    rw [ih]
    grind

#check Nat.rec -- The full dependent recursor (needed for the proofs;
-- for the construction of mathematical objects, constant motives are enough)
-- Nat.rec.{u} {motive : ℕ → Sort u}
-- (zero : motive Nat.zero) (succ : (n : ℕ) → motive n → motive n.succ) (t : ℕ) :
-- motive t

def psum' (a : ℕ → ℝ) : ℕ → ℝ :=
  let motive : ℕ → Type := fun _ => ℝ -- (constant) type-valued motive
  Nat.rec
    (motive := motive) -- here we could do without giving explicitly the motive
    (zero := 0)
    (succ := fun n sum_n => sum_n + a n)

def natCast' := psum' (fun _ => 1) -- just add ones.

theorem natCast'_eq : natCast' = Nat.cast := by
  let motive (n : ℕ) : Prop := natCast' n = Nat.cast n -- not constant!
  let p := Nat.rec
    (motive := motive) -- here we *need* and explicit motive
    (zero := show
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

example : ∀ n, (psum' natCast') n = n * (n - 1) / 2 :=
  let motive (n : ℕ) : Prop := (psum' natCast') n = n * (n - 1) / 2
  Nat.rec
    (motive := motive)
    (zero := show motive 0 from by
      simp only [motive]
      rw [psum']
      simp only -- uses Nat.rec_zero
      norm_num
    )
    (succ := show (n : ℕ) → motive n → motive (n + 1) from by
      simp only [motive]
      intro n hn
      rw [psum']
      simp only -- uses Nat.rec_add_one
      rw [<- psum']
      rw [hn]
      rw [natCast'_eq]
      grind
    )

#print Tree
-- inductive Tree.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- Tree.nil : {α : Type u} → Tree α
-- Tree.node : {α : Type u} → α → Tree α → Tree α → Tree α

#check Tree.rec
-- Tree.rec.{u_1, u} {α : Type u} {motive : Tree α → Sort u_1}
--     (nil : motive Tree.nil)
--     (node :
--       (a : α) →
--       (a_1 a_2 : Tree α) →
--       motive a_1 → motive a_2 →
--       motive (Tree.node a a_1 a_2)
--     )
--     (t : Tree α) : motive t

-- TODO: define # of nodes and depth and compare (using recursion)

def Tree.count {α} (t : Tree α) : ℕ := -- i.e. Tree.numNodes in Mathlib
  match t with
  | nil => 0
  | node _ t1 t2 => Tree.count t1 + Tree.count t2 + 1

def Tree.depth {α} (t : Tree α) : ℕ := -- i.e. Tree.height in Mathlib
  match t with
  | nil => 0
  | node _ t1 t2 => max (Tree.depth t1) (Tree.depth t2) + 1

lemma max_le_add : max (α := ℕ) ≤ Nat.add := by
  intro m n
  simp only [Nat.max_def]
  grind

example {α} : ∀ (t : Tree α), t.depth ≤ t.count := by
  intro t
  induction t with
  | nil =>
    rw [Tree.depth, Tree.count]
  | node _ t1 t2 ih1 ih2 =>
    rw [Tree.depth, Tree.count]
    -- ⊢ max t1.depth t2.depth + 1 ≤ t1.count + t2.count + 1
    have : max t1.depth t2.depth + 1 ≤ t1.depth + t2.depth + 1 := by
      simp only [add_le_add_iff_right]
      apply max_le_add
    apply le_trans this
    linarith
