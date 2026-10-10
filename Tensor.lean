/-!
Type-safe tensors computations (if I can do Lin, ReLu and Softmax I am happy...)
-/

abbrev Shape := List Nat

def Index (shape : Shape) : Type :=
  match shape with
  | []     => Unit
  | n :: s => Fin n × Index s

#check ((1, 2, 3, ()) : Index [8, 8, 8]) -- That's a bit weird!
-- Can we cheat and avoid the trailing unit ? Probably, yes,
-- but let's keep that pure/simple ATM. (We rarely need to get
-- the index "by hand")

-- Mmmmm ... ok.
structure Tensor (shape : Shape) : Type where
  data : Array Float
  size_data : data.size = shape.prod

#check Array.size_replicate
-- Array.size_replicate.{u_1} {α : Type u_1} {n : Nat} {v : α} :
-- (Array.replicate n v).size = n

def Tensor.default (shape : Shape) : Tensor shape :=
  let data : Array Float := Array.replicate shape.prod (Inhabited.default : Float)
  have size_data : data.size = shape.prod := Array.size_replicate
  { data, size_data }

def Tensor.getElem {shape : Shape} (tensor : Tensor shape) (index : Index shape) : Float :=
  sorry

def Tensor.outerProduct {shape1 shape2 : Shape}
    (tensor1 : Tensor shape1) (tensor2 : Tensor shape2) :
    Tensor (shape1 ++ shape2) :=
  sorry

-- TODO: operations on a shape that removes indices (util. to deal with
-- shape contraction)

def Tensor.contract {shape : Shape}
    (tensor : Tensor shape)
    (axis1 axis2 : Fin shape.length)
    (h : axis1 ≠ axis2)
    (h' : shape[axis1] = shape[axis2]) :
    sorry := sorry

/-!
TODO:
  - outer product ⊗
  - contraction (pair of indices)
  - index permutation
  - addition and scalar mul
  - "generators" (default, kroneck delta, etc.? From function?)
-/

/-!
TODO:
  - Linear (Affine),
  - ReLu
  - Softmax
-/
