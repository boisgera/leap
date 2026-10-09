/-!
Type-safe tensors computations (if I can do Lin, ReLu and Softmax I am happy...)
-/

abbrev Shape := List Nat

def Index (shape : Shape) : Type :=
  match shape with
  | []     => Unit
  | n :: s => Fin n × Index s

#check ((1, 2, 3, ()) : Index [8, 8, 8]) -- That's a bit weird!
-- Can we cheat and avoid the trailing unit ? Probably, yes.
-- (even if it's *arguably* less pure / consistent...)
-- So what do we do?

-- Mmmmm ...
structure Tensor (shape : Shape) : Type where
  array : Array Float
  array_size : array.size = shape.prod

#check Array.size_replicate
-- Array.size_replicate.{u_1} {α : Type u_1} {n : Nat} {v : α} :
-- (Array.replicate n v).size = n

def Tensor.default (shape : Shape) : Tensor shape :=
  let array : Array Float := Array.replicate shape.prod (Inhabited.default : Float)
  have array_size : array.size = shape.prod := Array.size_replicate
  { array, array_size }

def Tensor.getElement {shape : Shape} (tensor : Tensor shape) (index : Index shape) : Float :=
  sorry
