#print List
-- inductive List.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- List.nil : {α : Type u} → List α
-- List.cons : {α : Type u} → α → List α → List α

inductive NonEmptyList.{u} (α : Type u) where
| singleton : (a : α) -> NonEmptyList α
| cons : (a : α) -> NonEmptyList α -> NonEmptyList α
deriving Repr

namespace NonEmptyList

scoped infixr:67 " :: " => NonEmptyList.cons

-- Three interestings ways to bridge from List to NonEmptyList:
-- panic!, Option or proof

#check List.head!
-- List.head!.{u_1} {α : Type u_1} [Inhabited α] : List α → α

#check List.head?
-- List.head?.{u} {α : Type u} : List α → Option α

#check List.head
-- List.head.{u} {α : Type u} (as : List α) : as ≠ [] → α

instance {α} [Inhabited α] : Inhabited (NonEmptyList α) where
  default := NonEmptyList.singleton default

def fromList! {α} [Inhabited α] (l : List α) : NonEmptyList α :=
  match l with
  | [] => panic! "empty list"
  | a1 :: [] => NonEmptyList.singleton a1
  | a1 :: a2 :: tail => NonEmptyList.cons a1 (fromList! (a2 :: tail))

def fromList? {α} (l : List α) : Option (NonEmptyList α) :=
  match l with
  | [] => none
  | a :: tail =>
    match fromList? tail with
    | none => NonEmptyList.singleton a
    | some tail' => NonEmptyList.cons a tail'

def fromList {α} (l : List α) (nonEmpty : l ≠ []) : NonEmptyList α :=
  match l with
  | [] => nomatch nonEmpty
  | a1 :: [] => NonEmptyList.singleton a1
  | a1 :: a2 :: tail =>
    let tail' := a2 :: tail
    have nonEmptyTail' : (tail' ≠ []) := by grind
    NonEmptyList.cons a1 (fromList tail' nonEmptyTail')

end NonEmptyList

#eval NonEmptyList.fromList! [1, 2, 3]
-- NonEmptyList.cons 1 (NonEmptyList.cons 2 (NonEmptyList.singleton 3))

#eval NonEmptyList.fromList! ([] : List Nat)
-- PANIC at NonEmptyList.fromList!

#eval NonEmptyList.fromList? [1, 2, 3]
-- some (NonEmptyList.cons 1 (NonEmptyList.cons 2 (NonEmptyList.singleton 3)))

#eval NonEmptyList.fromList? ([] : List Nat)
-- none

#eval NonEmptyList.fromList [1, 2, 3] (by grind)
-- NonEmptyList.cons 1 (NonEmptyList.cons 2 (NonEmptyList.singleton 3))

-- and you can't provide the nonEmpty argument if l is []!
