import Mathlib

inductive IsSorted : List Int -> Prop where
| none : IsSorted []
| one : ∀ (n : Int), IsSorted [n]
| many : ∀ (m n : Int), ∀ (ns : List Int),
    m ≤ n -> IsSorted (n :: ns) -> IsSorted (m :: n :: ns)

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

/--
info: Multiset.coe_eq_coe.{u_1} {α : Type u_1} {l₁ l₂ : List α} :
↑l₁ = ↑l₂ ↔ l₁.Perm l₂
-/
#guard_msgs (whitespace := lax) in
#check Multiset.coe_eq_coe

-- TODO 🚧: state in terms of permutations directly, not multisets.
lemma sortInsert_multiset (n : Int) (ns : List Int) :
  Multiset.ofList (sortInsert n ns) = n ::ₘ Multiset.ofList ns := by
  induction ns with
  | nil =>
    simp [sortInsert]
  | cons m ns ih =>
    simp [sortInsert]
    split_ifs with h
    · -- Case: n ≤ m
      rfl
    · -- Case: ¬(n ≤ m)
      -- TODO 🚧
      --   - derive (sortInsert n ns).Perm (n :: ns) from ih : ↑(sortInsert n ns) = n ::ₘ ↑ns
      --   - derive (m :: sortInsert n ns).Perm (m :: n :: ns) from that
      --   - establish that (m :: n :: ns).Perm (n :: m :: ns)
      --   - by transitivity deduce the goal: (m :: sortInsert n ns).Perm (n :: m :: ns)
      admit




theorem multiseq_eq_multiset_sorted : ∀ (ns : List Int),
Multiset.ofList ns = Multiset.ofList (sort ns) := by
  intro ns
  induction ns with
  | nil =>
    simp [sort]
  | cons n ns ih =>
    rw [sort]
    rw [sortInsert_multiset]
    simp
    exact Multiset.coe_eq_coe.mp ih



-- We need some induction stuff on the list ns
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
