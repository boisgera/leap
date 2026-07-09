import Lean
import Batteries.Lean.Float

namespace Mesh

structure Point where
  x : Float
  y : Float
  z : Float

structure Vector where
  x : Float
  y : Float
  z : Float

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

-- TODO: support Point - Point, Point + Vector, etc.


structure Facet where
  point1 : Point
  point2 : Point
  point3 : Point

end Mesh


def main := IO.println "mesh"
