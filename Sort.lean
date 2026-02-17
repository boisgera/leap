import Mathlib

-- The proof of termination would be nice!
partial def quicksort {α} [LinearOrder α] [DecidableLE α] (as: List α) :=
  match h: as with
  | [] => as
  | [_] => as
  | [a1, a2] =>
    if a1 ≤ a2 then [a1, a2] else [a2, a1]
  | a1 :: a2 :: a3 :: tail =>
    have: as.length ≥ 1 := by grind
    let pivot := as[as.length / 2]'(by grind)
    -- This code suggest a more efficient, locally mutable approach to
    -- build these lists and the use of the Ord typeclass. See quicksort'
    -- below.
    let lt_p := as.filter (· < pivot)
    let eq_p := as.filter (· = pivot)
    let gt_p := as.filter (· > pivot)
    quicksort lt_p ++ eq_p ++ quicksort gt_p

#eval quicksort [1, 10, -6, 0, 12, -56, 100]

-- Note: it *may* be a better design to return an Ordering -> List α
-- See below; I am not sure it's actually better.
def split {α} [Ord α] (as : List α) (pivot : α) :
    (List α) × (List α) × (List α) := Id.run do
  let mut lt_pivot : List α := []
  let mut eq_pivot : List α := []
  let mut gt_pivot : List α := []

  for a in as do
    match compare a pivot with
    | .lt => lt_pivot := a :: lt_pivot
    | .eq => eq_pivot := a :: eq_pivot
    | .gt => gt_pivot := a :: gt_pivot
  return (lt_pivot, eq_pivot, gt_pivot)

partial def quicksort' {α} [Ord α] (as: List α) : List α :=
  match h : as with
  | [] | [a1] => as
  | [a1, a2] =>
    if compare a1 a2 = .gt then [a2, a1] else [a1, a2]
  | a1 :: a2 :: a3 :: tail =>
    let pivot := as[as.length / 2]'(by grind)
    let (lt_pivot, eq_pivot, gt_pivot) := split as pivot
    quicksort' lt_pivot ++ eq_pivot ++ quicksort' gt_pivot

--

def split' {α} [Ord α] (as : List α) (pivot : α) :
    Ordering -> List α := Id.run do
  let mut lt_pivot : List α := []
  let mut eq_pivot : List α := []
  let mut gt_pivot : List α := []

  for a in as do
    match compare a pivot with
    | .lt => lt_pivot := a :: lt_pivot
    | .eq => eq_pivot := a :: eq_pivot
    | .gt => gt_pivot := a :: gt_pivot
  let list (ordering : Ordering) : List α :=
    match ordering with
    | .lt => lt_pivot
    | .eq => eq_pivot
    | .gt => gt_pivot
  return list

partial def quicksort'' {α} [Ord α] (as: List α) : List α :=
  match h : as with
  | [] | [a1] => as
  | [a1, a2] =>
    if compare a1 a2 = .gt then [a2, a1] else [a1, a2]
  | a1 :: a2 :: a3 :: tail =>
    let pivot := as[as.length / 2]'(by grind)
    let list := split' as pivot
    quicksort'' (list .lt) ++ (list .eq) ++ quicksort'' (list .gt)
