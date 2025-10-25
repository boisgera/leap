#check Eq.subst

#check Eq.rec
-- Eq.rec.{u, u_1} {α : Sort u_1} {a✝ : α} {motive : (a : α) → a✝ = a → Sort u} (refl : motive a✝ ⋯) {a✝¹ : α}
--   (t : a✝ = a✝¹) : motive a✝¹ t

inductive Eq'.{u} {α : Type u} : α → α → Prop where
  | refl (a : α) : Eq' a a

#check Eq'.rec
-- Eq'.rec.{u_1, u} {α : Type u} {a✝ : α} {motive : (a : α) → Eq' a✝ a → Sort u_1}
-- (refl : motive a✝ ⋯) {a✝¹ : α}
-- (t : Eq' a✝ a✝¹) : motive a✝¹ t

inductive A : Nat -> Nat -> Sort where
  | intro (m n : Nat) : A m n

#check A.rec
-- A.rec.{u} {a✝ a✝¹ : Nat} {motive : A a✝ a✝¹ → Sort u} (intro : motive ⋯) (t : A a✝ a✝¹) : motive t

inductive A' (m : Nat) : Nat -> Sort where
  | intro (n : Nat) : A' m n

#check A'.rec
-- A'.rec.{u} {m a✝ : Nat} {motive : A' m a✝ → Sort u} (intro : motive ⋯) (t : A' m a✝) : motive t

inductive B : Nat -> Nat -> Sort where
  | intro (m n : Nat) : B m n
  | outro (n : Nat) : B n 1

#check B.rec
-- B.rec {a✝ : Nat} {motive : (a : Nat) → B a✝ a → Prop} (intro : ∀ (n : Nat), motive n ⋯)
-- (outro : motive 1 ⋯) {a✝¹ : Nat}
-- (t : B a✝ a✝¹) : motive a✝¹ t

inductive N where
  | zero : N
  | succ (n : N) : N

#check N.rec
-- N.rec.{u} {motive : N → Sort u}
--   (zero : motive N.zero)
--   (succ : (n : N) → motive n → motive n.succ)
--   (t : N)
--   : motive t
