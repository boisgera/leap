-- Source: https://arxiv.org/abs/2509.15015

import Mathlib

def sortInsert (n : Int) (ns : List Int) : List Int :=
  match ns with
  | [] => n :: []
  | m :: ns => if n <= m then
      n :: m :: ns
    else
      m :: (sortInsert n ns)

def sort (ns : List Int) : List Int :=
  match ns with
  | [] => []
  | n :: ns => sortInsert n (sort ns)

#eval sort [1, 2, 3]
-- [1, 2, 3]

#eval sort [5, 0, 2, 1, 3, 4]
-- [0, 1, 2, 3, 4, 5]

inductive IsSorted : List Int -> Prop where
| none : IsSorted []
| one : ∀ (n : Int), IsSorted [n]
| many : ∀ (m n : Int), ∀ (ns : List Int),
    m ≤ n -> IsSorted (n :: ns) -> IsSorted (m :: n :: ns)

def is_sorted (ns : List Int) :=
  ∀ (i : ℕ), ∀ (j : ℕ),
  (hi : i < ns.length) -> (hj : j < ns.length) ->
  (i <= j) -> ns[i]'hi <= ns[j]

theorem lemma_is_sorted_cons_is_sorted {n : Int} {ns : List Int}:
is_sorted (n :: ns) -> is_sorted (ns) := by
    intro is_sorted_n_ns
    rw [is_sorted] at *
    intro i j hi hj i_le_j
    have h := is_sorted_n_ns (i + 1) (j + 1)
    simp at h
    exact h hi hj i_le_j

theorem is_sorted_iff_IsSorted : ∀ (ns : List Int),
  is_sorted ns <-> IsSorted ns := by
  intro ns
  constructor
  . intro is_sorted_ns
    induction ns with
    | nil => exact IsSorted.none
    | cons n ns h =>
      cases ns with
      | nil => exact IsSorted.one n
      | cons m ms =>
          have IsSorted_m_ms := h (lemma_is_sorted_cons_is_sorted is_sorted_ns)
          have n_le_m : n <= m := by
            apply is_sorted_ns 0 1 _ _ _
            . simp
            . simp
            . simp
          exact IsSorted.many n m ms n_le_m IsSorted_m_ms
  . intro IsSorted_ns
    induction IsSorted_ns with
    | none =>
        rw [is_sorted]
        simp
    | one n =>
        rw [is_sorted]
        simp
    | many m n ns m_le_n IsSorted_n_ns ih =>
        rw [is_sorted]
        simp_all
        intro i j hi hj i_le_j
        cases i with
        | zero =>
          simp
          cases j with
          | zero => simp
          | succ j =>
            cases j with
            | zero => simp; exact m_le_n
            | succ j =>
              simp
              simp at hj
              clear i_le_j
              apply le_trans m_le_n
              rw [is_sorted] at ih
              apply ih 0 (j+1) (by grind) (by grind)
              simp
        | succ i =>
          simp at hi hi ⊢
          cases j with
          | zero => grind
          | succ j =>
            simp
            apply ih
            . grind

#check le_trans
-- le_trans.{u_1} {α : Type u_1} [Preorder α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c

lemma sortInsert_perm (n : Int) (ns : List Int) :
  (sortInsert n ns).Perm (n :: ns) := by
  induction ns with
  | nil =>
    rw [sortInsert]
  | cons m ns ih =>
    rw [sortInsert]
    split_ifs with h
    · -- n ≤ m
      rfl
    · -- ¬(n ≤ m)
      have h' : (m :: sortInsert n ns).Perm (m :: n :: ns) := by
        simp [List.perm_cons]
        exact ih
      have h'' : (m :: n :: ns).Perm (n :: m :: ns) := by
        exact List.Perm.swap n m ns
      exact List.Perm.trans h' h''

theorem multiseq_eq_multiset_sorted : ∀ (ns : List Int), ns.Perm (sort ns) := by
  intro ns
  induction ns with
  | nil =>
    simp [sort]
  | cons n ns ih =>
    rw [sort]
    have h := List.Perm.symm (sortInsert_perm n (sort ns))
    have h' := List.Perm.cons n ih
    exact List.Perm.trans h' h

theorem is_sorted_sort_insert (n : Int) (ns : List Int) (h : IsSorted ns) :
  IsSorted (sortInsert n ns) := by
  induction ns with
  | nil =>
    rw [sortInsert.eq_def]
    simp
    exact IsSorted.one n
  | cons m ms h' =>
    rw [sortInsert.eq_def]
    simp
    by_cases h'' : n <= m
    . simp [h'']
      exact (IsSorted.many n m ms h'' h)
    . simp [h'']
      have lemma : m <= n :=
        h'' |> Nat.not_le.mp |> Nat.le_of_lt -- Shit, we need MathLib for this stuff...
      have lemma' : IsSorted ms := by
        cases h with
        | one p => exact IsSorted.none
        | many m' n' ns' h1 h2 => exact h2
      have lemma'' : IsSorted (sortInsert n ms) :=
        h' lemma'
      admit


theorem is_sorted_sort : ∀ (ns : List Int), IsSorted (sort ns) := by
  intro ns
  induction ns with
  | nil =>
    rw [sort]
    exact IsSorted.none
  | cons n ns h =>
    rw [sort]
    rw [sortInsert.eq_def]

    admit
