
-- TODO: lose the genericity, make it a Zipper of Nats.
-- This is more elementary and will suppress the inhabited
-- stuff issue that comes with panic!

structure Zipper (α : Type u) where
  before : List α
  current : α
  after : List α
deriving Inhabited

instance {α} [Inhabited α] : Inhabited (Zipper α) where
  default := ⟨[], default, []⟩

namespace Zipper

def fromSingleton {α} (a : α) :=
  Zipper.mk [] a []

def fromList {α} [Inhabited α] (l : List α) : Zipper α :=
  match l with
  | [] => panic! "The list is empty"
  | head :: tail => Zipper.mk [] head tail

def toList {α} (z : Zipper α) : List α :=
  z.before.reverse ++ (z.current :: z.after)

def get {α} (z : Zipper α) := z.current

def set {α} (z : Zipper α) (a : α) :=
  Zipper.mk z.before a z.after

def goLeft {α} (z : Zipper α) :=
  match z.before with
  | [] => z
  | head :: tail => Zipper.mk tail head (z.current :: z.after)

def goRight {α} (z : Zipper α) :=
  match z.after with
  | [] => z
  | head :: tail => Zipper.mk (z.current :: z.before) head tail

def insertBefore {α} (z : Zipper α) (a : α) :=
  Zipper.mk (a :: z.before) z.current z.after

def insertAfter {α} (z : Zipper α) (a : α) :=
  Zipper.mk z.before z.current (a :: z.after)

instance {α} [ToString α] : ToString (Zipper α) where
  toString := fun (z : Zipper α) =>
    let before := toString z.before.reverse
    let current := s!"[{z.current}]"
    let after := toString z.after
    s!"{before} {current} {after}"

end Zipper

#check Zipper.fromList [0, 1, 2, 3]

#eval Zipper.fromList [0, 1, 2, 3]
-- [] [0] [1, 2, 3]

#eval Zipper.fromList [0, 1, 2, 3] |>.goRight |>.goRight
-- [0, 1] [2] [3]

#eval Zipper.fromList [0, 1, 2, 3] |>.goRight |>.goRight |>.insertBefore 4
-- [0, 1, 4] [2] [3]

#eval Zipper.fromList [0, 1, 2, 3]
  |>.goRight
  |>.goRight
  |>.insertBefore 4
  |>.insertAfter 5
-- [0, 1, 4] [2] [5, 3]
