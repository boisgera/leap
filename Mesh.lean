import Lean
import Batteries.Lean.Float

namespace STL

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

def Vector.origin := Vector.mk 0 0 0

instance : Inhabited Vector where
  default := Vector.origin

def Vector.toSTL (u : Vector) : String :=
  s!"{u.1.toStringFull} {u.2.toStringFull} {u.3.toStringFull}"

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

def Point.origin : Point := Point.mk 0 0 0

instance : Inhabited Point where
  default := Point.origin

def Point.toSTL (p : Point) : String :=
  s!"{p.1.toStringFull} {p.2.toStringFull} {p.3.toStringFull}"

def Point.sub (q p : Point) : Vector :=
  Vector.mk (q.x - p.x) (q.y - p.y) (q.z - p.z)

instance : HSub Point Point Vector where
  hSub := Point.sub

#eval (Point.mk 1.0 2.0 3.0) - (Point.mk (-1.0) (-1.0) (-1.0))
-- { x := 2.000000, y := 3.000000, z := 4.000000 }

def Point.add (p : Point) (u : Vector) : Point :=
  Point.mk (p.x + u.x) (p.y + u.y) (p.z + u.z)

instance : HAdd Point Vector Point where
  hAdd := Point.add

#eval (Point.mk 1 1 1) + (Vector.mk 1 2 3)
-- { x := 2.000000, y := 3.000000, z := 4.000000 }

structure Facet where
  vertex_1 : Point -- The f.1 notation is for free
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

def Facet.toSTL (f : Facet) : String :=
s!"facet normal {f.normal.toSTL}
    outer loop
        vertex {f.1.toSTL}
        vertex {f.2.toSTL}
        vertex {f.3.toSTL}
    endloop
endfacet"

-- not sure we need a new type here...
structure Quad where
  vertex_1 : Point
  vertex_2 : Point
  vertex_3 : Point
  vertex_4 : Point

def Quad.toList (q : Quad) : List Point :=
  [q.vertex_1, q.vertex_2, q.vertex_3, q.vertex_4]

def weightedSum (elts : List (Float × Point))
    (origin : Point := default) : Point :=
  -- form the vectors origin-to-points
  let weightedVectors := elts.map (fun (w, p) => (w, p - origin))
  -- combine the vectors
  let weightedPoint := weightedVectors.foldl
    (f := fun p (w, v) => p + w • v)
    (init := (origin : Point))
  weightedPoint

#eval weightedSum [(0.5, (Point.mk 1 2 3)), (0.5, (Point.mk 3 2 1))]
-- { x := 2.000000, y := 2.000000, z := 2.000000 }

#eval weightedSum [
  (0.25, Point.mk 0 0 0),
  (0.25, Point.mk 1 0 0),
  (0.25, Point.mk 1 1 0),
  (0.25, Point.mk 0 1 0),
]
-- { x := 0.500000, y := 0.500000, z := 0.000000 }

def Quad.split (q : Quad) : List Facet :=
  let center := q.toList.map (fun p => (0.25, p)) |> weightedSum
  [
    Facet.mk q.1 q.2 center,
    Facet.mk q.2 q.3 center,
    Facet.mk q.3 q.4 center,
    Facet.mk q.4 q.1 center,
  ]



structure Mesh where
  facets : List Facet

def Mesh.toSTL (m : Mesh) (name : String := "") : String :=
  let facetsSTL := m.facets |>.map (fun f => f.toSTL) |> String.intercalate "\n"
  s!"solid {name}\n{facetsSTL}\nendsolid {name}"


-- TODO: STL export

def test_facet :=
  Mesh.mk [Facet.mk (Point.mk 0 0 0) (Point.mk 1 0 0) (Point.mk 0 1 0)]
  |>.toSTL
  |> IO.println

#eval test_facet
-- solid
-- facet normal 0 0 1
--     outer loop
--         vertex 0 0 0
--         vertex 1 0 0
--         vertex 0 1 0
--     endloop
-- endfacet
-- endsolid

def test_cube := do
  let p_1 := Point.mk 0 0 0
  let p_2 := Point.mk 1 0 0
  let p_3 := Point.mk 1 1 0
  let p_4 := Point.mk 0 1 0
  let p_5 := Point.mk 0 0 1
  let p_6 := Point.mk 1 0 1
  let p_7 := Point.mk 1 1 1
  let p_8 := Point.mk 0 1 1
  let quad_1 := Quad.mk p_1 p_4 p_3 p_2
  let quad_2 := Quad.mk p_1 p_2 p_6 p_5
  let quad_3 := Quad.mk p_2 p_3 p_7 p_6
  let quad_4 := Quad.mk p_3 p_4 p_8 p_7
  let quad_5 := Quad.mk p_4 p_1 p_5 p_8
  let quad_6 := Quad.mk p_5 p_6 p_7 p_8
  let facets :=
    quad_1.split ++
    quad_2.split ++
    quad_3.split ++
    quad_4.split ++
    quad_5.split ++
    quad_6.split
  let mesh := Mesh.mk facets
  let meshSTL := mesh.toSTL "cube"
  meshSTL |> IO.println
  IO.FS.writeFile "cube.stl" meshSTL

-- TODO:
-- given a SDF and a quantized 3D range, get the active edges (with sign change)
-- collect the corresponding quad and build the mesh.
-- How do we deal with the fact that we don't want to have all (active and non
-- active) edges in memory at the same time? Try a first version where we don't
-- care? The iterator API is frightening ...

def meshOfSdf
  (f : Float → Float → Float → Float)
  (min max : Point) (step : Float) : Mesh :=
  sorry


end STL


def main := do
  STL.test_cube
-- solid cube
-- facet normal 0 0 -1
--     outer loop
--         vertex 0 0 0
--         vertex 0 1 0
--         vertex 0.5 0.5 0
--     endloop
-- endfacet
-- facet normal 0 0 -1
--     outer loop
--         vertex 0 1 0
--         vertex 1 1 0
--         vertex 0.5 0.5 0
--     endloop
-- endfacet
-- facet normal 0 0 -1
--     outer loop
--         vertex 1 1 0
--         vertex 1 0 0
--         vertex 0.5 0.5 0
--     endloop
-- endfacet
-- facet normal 0 0 -1
--     outer loop
--         vertex 1 0 0
--         vertex 0 0 0
--         vertex 0.5 0.5 0
--     endloop
-- endfacet
-- facet normal 1 0 0
--     outer loop
--         vertex 0 0 0
--         vertex 0 1 0
--         vertex 0 0.5 0.5
--     endloop
-- endfacet
-- facet normal 1 0 0
--     outer loop
--         vertex 0 1 0
--         vertex 0 1 1
--         vertex 0 0.5 0.5
--     endloop
-- endfacet
-- facet normal 1 0 0
--     outer loop
--         vertex 0 1 1
--         vertex 0 0 1
--         vertex 0 0.5 0.5
--     endloop
-- endfacet
-- facet normal 1 0 0
--     outer loop
--         vertex 0 0 1
--         vertex 0 0 0
--         vertex 0 0.5 0.5
--     endloop
-- endfacet
-- facet normal 0 -1 0
--     outer loop
--         vertex 0 1 0
--         vertex 1 1 0
--         vertex 0.5 1 0.5
--     endloop
-- endfacet
-- facet normal 0 -1 0
--     outer loop
--         vertex 1 1 0
--         vertex 1 1 1
--         vertex 0.5 1 0.5
--     endloop
-- endfacet
-- facet normal 0 -1 0
--     outer loop
--         vertex 1 1 1
--         vertex 0 1 1
--         vertex 0.5 1 0.5
--     endloop
-- endfacet
-- facet normal 0 -1 0
--     outer loop
--         vertex 0 1 1
--         vertex 0 1 0
--         vertex 0.5 1 0.5
--     endloop
-- endfacet
-- facet normal -1 0 0
--     outer loop
--         vertex 1 1 0
--         vertex 1 0 0
--         vertex 1 0.5 0.5
--     endloop
-- endfacet
-- facet normal -1 0 0
--     outer loop
--         vertex 1 0 0
--         vertex 1 0 1
--         vertex 1 0.5 0.5
--     endloop
-- endfacet
-- facet normal -1 0 0
--     outer loop
--         vertex 1 0 1
--         vertex 1 1 1
--         vertex 1 0.5 0.5
--     endloop
-- endfacet
-- facet normal -1 0 0
--     outer loop
--         vertex 1 1 1
--         vertex 1 1 0
--         vertex 1 0.5 0.5
--     endloop
-- endfacet
-- facet normal 0 1 0
--     outer loop
--         vertex 1 0 0
--         vertex 0 0 0
--         vertex 0.5 0 0.5
--     endloop
-- endfacet
-- facet normal 0 1 0
--     outer loop
--         vertex 0 0 0
--         vertex 0 0 1
--         vertex 0.5 0 0.5
--     endloop
-- endfacet
-- facet normal 0 1 0
--     outer loop
--         vertex 0 0 1
--         vertex 1 0 1
--         vertex 0.5 0 0.5
--     endloop
-- endfacet
-- facet normal 0 1 0
--     outer loop
--         vertex 1 0 1
--         vertex 1 0 0
--         vertex 0.5 0 0.5
--     endloop
-- endfacet
-- facet normal 0 0 -1
--     outer loop
--         vertex 0 0 1
--         vertex 0 1 1
--         vertex 0.5 0.5 1
--     endloop
-- endfacet
-- facet normal 0 0 -1
--     outer loop
--         vertex 0 1 1
--         vertex 1 1 1
--         vertex 0.5 0.5 1
--     endloop
-- endfacet
-- facet normal 0 0 -1
--     outer loop
--         vertex 1 1 1
--         vertex 1 0 1
--         vertex 0.5 0.5 1
--     endloop
-- endfacet
-- facet normal 0 0 -1
--     outer loop
--         vertex 1 0 1
--         vertex 0 0 1
--         vertex 0.5 0.5 1
--     endloop
-- endfacet
-- endsolid cube
