import Mathlib

/-!
Type-safe tensors computations (if I can do Lin, ReLu and Softmax I am happy...)
-/

abbrev Shape := List Nat

def Index (shape : Shape) : Type :=
  match shape with
  | []     => Unit
  | n :: s => Fin n × Index s

#check ((1, 2, 3, ()) : Index [8, 8, 8]) -- That's *a bit* weird!
-- Can we cheat and avoid the trailing unit ? Probably, yes,
-- but let's keep that pure/simple ATM. (We rarely need to get
-- the index "by hand")

structure Tensor (shape : Shape) : Type where
  data : Array Float
  size_data : data.size = shape.prod

def Tensor.toString {shape : Shape} (tensor : Tensor shape) : String :=
  ToString.toString tensor.data.toList

instance {shape : Shape} : ToString (Tensor shape) where
  toString := Tensor.toString

#check Array.size_replicate
-- Array.size_replicate.{u_1} {α : Type u_1} {n : Nat} {v : α} :
-- (Array.replicate n v).size = n

def Tensor.zeros {shape : Shape} : Tensor shape :=
  let data : Array Float := Array.replicate shape.prod 0.0
  have size_data : data.size = shape.prod := Array.size_replicate
  { data, size_data }

instance {shape : Shape} : Inhabited (Tensor shape) where
  default := Tensor.zeros

#eval (Tensor.zeros : Tensor [2, 3])

/-!
There is a small issue to solve: when shape = [], the only possible
index is Unit.unit, which makes sense (non-informative), but then
so far, we have raw_index = 0, which contradicts raw_index < array.size.
Sooooo at some stage we have to exclude Tensors with an empty shape.
And at the GetElem level also (doesn't make sense), so we have to
reintroduce the validity proposition in the typeclass.
-/

def Tensor.raw_index {shape : Shape} (index : Index shape) : Nat :=
  match shape, index with
  | [], _ => 0
  | _ :: shape, (i, index) => i * shape.prod + (Tensor.raw_index index)

theorem Tensor.raw_index_lt {shape : Shape} (index : Index shape) :
  raw_index index < shape.prod := by
  induction shape with
  | nil =>
    simp only [List.prod_nil, Nat.lt_one_iff]
    rw [raw_index]
  | cons n shape tail_ih =>
    let (i, index_tail) := index
    rw [raw_index]
    simp only [List.prod_cons, gt_iff_lt]
    have : ↑i < n := i.isLt
    specialize tail_ih index_tail
    linarith -- normal that it fails: doesn't work when shape = []

def Tensor.getElem {shape : Shape} (tensor : Tensor shape) (index : Index shape) : Float :=
  let i := Tensor.raw_index index
  have i_lt : i < tensor.data.size := by
    simp only [Tensor.size_data, i, Tensor.raw_index_lt]
  tensor.data[i]'i_lt

#print GetElem
-- class GetElem.{u, v, w} (coll : Type u) (idx : Type v) (elem : outParam (Type w))
--   (valid : outParam (coll → idx → Prop)) : Type (max (max u v) w)
-- number of parameters: 4
-- fields:
--   GetElem.getElem : (xs : coll) → (i : idx) → valid xs i → elem
-- constructor:
--   GetElem.mk.{u, v, w} {coll : Type u} {idx : Type v} {elem : outParam (Type w)} {valid : outParam (coll → idx → Prop)}
--     (getElem : (xs : coll) → (i : idx) → valid xs i → elem) : GetElem coll idx elem valid

instance {shape : Shape} : GetElem (Tensor shape) (Index shape) Float (fun _tensor _index => True) where
  getElem (tensor : Tensor shape) (index : Index shape) (_ : True) := tensor.getElem index


def t : Tensor [3, 2] := {
  data := #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0],
  size_data := by simp
}

def i : Index [3, 2] := (0, 0, ())

#eval! t[i]
-- 1.000000

/-!
Much harder after this point I guess ...
-/

def Tensor.outerProduct {shape1 shape2 : Shape}
    (tensor1 : Tensor shape1) (tensor2 : Tensor shape2) :
    Tensor (shape1 ++ shape2) :=
  sorry

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
