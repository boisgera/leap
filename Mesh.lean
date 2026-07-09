import Lean
import Batteries.Lean.Float

namespace Mesh

structure Point where
  x : Float
  y : Float
  z : Float
deriving Repr

structure Vector where
  x : Float
  y : Float
  z : Float
deriving Repr

#eval Vector.mk 1.0 2.0 3.0
-- { x := 1.000000, y := 2.000000, z := 3.000000 }

#eval Float.toString (0.1 + 0.2)
-- "0.300000"

#eval Float.toStringFull (0.1 + 0.2)
-- "0.3000000000000000444089209850062616169452667236328125"

def Vector.add (u v : Vector) : Vector :=
  {
    x := u.x + v.x,
    y := u.y + u.y,
    z := u.z + v.z,
  }

instance : Add Vector where
  add := Vector.add

#eval Vector.mk 1.0 2.0 3.0 + Vector.mk 0.0 1.0 2.0
-- { x := 1.000000, y := 4.000000, z := 5.000000 }

def Vector.smul (s : Float) (u : Vector) : Vector :=
  {
    x := s * u.x,
    y := s * u.y,
    z := s * u.z,
  }

instance : SMul Float Vector where
  smul := Vector.smul

#eval (2.0 : Float) • (Vector.mk 1.0 2.0 3.0)
-- { x := 2.000000, y := 4.000000, z := 6.000000 }

def Vector.crossProduct (u v : Vector) : Vector :=
  {
    x := u.y * v.z - u.z * v.y,
    y := u.z * v.x - u.x * v.z,
    z := u.x * v.y - u.y * v.x,
  }

infixl:70 " ⨯ " => Vector.crossProduct

#eval Vector.mk 2.0 0.0 0.0 ⨯ Vector.mk 0.0 3.0 0.0
-- { x := 0.000000, y := 0.000000, z := 6.000000 }

def Vector.norm (u : Vector) : Float :=
  Float.sqrt (u.x * u.x + u.y * u.y + u.z * u.z)

notation:max "‖" x "‖" => Vector.norm x

#eval ‖Vector.mk 1.0 1.0 1.0‖
-- 1.732051

def Point.sub (q p : Point) : Vector :=
  Vector.mk (q.x - p.x) (q.y - p.y) (q.z - p.z)

instance : HSub Point Point Vector where
  hSub := Point.sub

#eval (Point.mk 1.0 2.0 3.0) - (Point.mk (-1.0) (-1.0) (-1.0))
-- { x := 2.000000, y := 3.000000, z := 4.000000 }

structure Facet where
  vertex_1 : Point -- can I have f.1 notation? Or even f[1]?
  vertex_2 : Point
  vertex_3 : Point
deriving Repr

def Facet.normal (f : Facet) : Vector :=
  let u := f.2 - f.1
  let v := f.3 - f.1
  let w := u ⨯ v
  (1 / ‖w‖) • w

def facet := Facet.mk (Point.mk 0 0 0) (Point.mk 1.0 0.0 0.0) (Point.mk 0.0 1.0 0.0)

#eval facet
-- { vertex_1 := { x := 0.000000, y := 0.000000, z := 0.000000 },
--   vertex_2 := { x := 1.000000, y := 0.000000, z := 0.000000 },
--   vertex_3 := { x := 0.000000, y := 1.000000, z := 0.000000 } }

#check facet.normal
-- facet.normal : Vector

#eval facet.normal
-- { x := 0.000000, y := 0.000000, z := 1.000000 }

end Mesh

structure Mesh where
  facets : List Mesh.Facet

-- TODO: STL export

def main := IO.println "mesh"
