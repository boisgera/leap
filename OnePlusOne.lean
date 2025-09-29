import Mathlib

namespace Sandbox

inductive Nat where
| zero
| succ (n : Nat)

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n => (add m n).succ


#reduce add Nat.zero.succ Nat.zero.succ
-- Nat.zero.succ.succ

theorem one_plus_one_eq_two : add (Nat.zero.succ) (Nat.zero.succ) = Nat.zero.succ.succ := by
  rewrite [add]
  rewrite [add]
  rfl

#print one_plus_one_eq_two
-- theorem Sandbox.one_plus_one_eq_two : add Nat.zero.succ Nat.zero.succ = Nat.zero.succ.succ :=
-- Eq.mpr (id (congrArg (fun _a => _a = Nat.zero.succ.succ) (add.eq_2 Nat.zero.succ Nat.zero)))
--   (Eq.mpr (id (congrArg (fun _a => _a.succ = Nat.zero.succ.succ) (add.eq_1 Nat.zero.succ)))
--     (Eq.refl Nat.zero.succ.succ))

#check Eq.mpr
-- Eq.mpr.{u} {α β : Sort u} (h : α = β) (b : β) : α

#check id
-- id.{u} {α : Sort u} (a : α) : α

#check congrArg
-- congrArg.{u, v} {α : Sort u} {β : Sort v} {a₁ a₂ : α}
-- (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂

#check add.eq_1
-- Sandbox.add.eq_1 (m : Nat) : add m Nat.zero = m

#check add.eq_2
-- Sandbox.add.eq_2 (m n_2 : Nat) : add m n_2.succ = (add m n_2).succ

theorem one_plus_one_eq_two' : add Nat.zero.succ Nat.zero.succ = Nat.zero.succ.succ :=
Eq.mpr
  (id
    (congrArg
      (fun _a => _a = Nat.zero.succ.succ)
      (add.eq_2 Nat.zero.succ Nat.zero)
    )
  )
  (Eq.mpr
    (id
      (congrArg
        (fun _a => _a.succ = Nat.zero.succ.succ)
        (add.eq_1 Nat.zero.succ))
      )
    (Eq.refl Nat.zero.succ.succ)
  )

theorem one_plus_one_eq_two'' : add Nat.zero.succ Nat.zero.succ = Nat.zero.succ.succ :=
  -- (1 + 0) +1 = 2
  have succ_one_add_zero_eq_two : (add Nat.zero.succ Nat.zero).succ = Nat.zero.succ.succ :=
    (Eq.mpr
      (id
        (congrArg
          (·.succ = Nat.zero.succ.succ)
          (add.eq_1 Nat.zero.succ)
        )
      )
      (Eq.refl Nat.zero.succ.succ)
  )
  -- ((1 + 0) +1 = 2)  =  (1 + 1 = 2)
  have one_add_one_eq_two_eq_succ_one_add_zero_eq_two:
  ((add Nat.zero.succ Nat.zero.succ) = Nat.zero.succ.succ) =
  ((add Nat.zero.succ Nat.zero).succ = Nat.zero.succ.succ) :=
    congrArg
      (· = Nat.zero.succ.succ)
      (add.eq_2 Nat.zero.succ Nat.zero)
  Eq.mpr (one_add_one_eq_two_eq_succ_one_add_zero_eq_two) (succ_one_add_zero_eq_two)

-- m + 0 = m
#check add.eq_1
-- Sandbox.add.eq_1 (m : Nat) : add m Nat.zero = m

-- m + (n +1) = (m + n) +1
#check add.eq_2
-- Sandbox.add.eq_2 (m n_2 : Nat) : add m n_2.succ = (add m n_2).succ

-- n + 1 = n +1
theorem add_one_eq_succ (n : Nat) : add n Nat.zero.succ = n.succ :=
  add.eq_2 n Nat.zero

-- 1 + 1 = 1 +1
theorem one_plus_one_eq_two''' : add Nat.zero.succ Nat.zero.succ = Nat.zero.succ.succ :=
  add_one_eq_succ Nat.zero.succ

theorem eq_of_succ_eq_succ {m n : Nat} : m.succ = n.succ -> m = n := by
  intro m_succ_eq_n_succ
  cases m_succ_eq_n_succ
  rfl

theorem succ_eq_succ_of_eq {m n : Nat} : m = n -> m.succ = n.succ := by
  intro m_eq_n
  exact congrArg Nat.succ m_eq_n

end Sandbox
