import Lean
import Batteries.Lean.Float -- provides Float.toStringFull

namespace STL

structure Point where
  x : Float
  y : Float
  z : Float
deriving BEq, Repr

structure Vector where
  x : Float
  y : Float
  z : Float
deriving BEq, Repr

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
deriving Inhabited

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


-- TODO: replace min and max by custom bbox type? There could be a funny
-- custom algebra of bbox when we do CSG stuff (union, inter, etc.).
structure Grid where
  min : Point
  max : Point
  step : Float
deriving Repr

structure Index where
  i : Int
  j : Int
  k : Int
deriving Repr

def Grid.imin (g : Grid) : Index :=
  let q := fun (x : Float) => (x / g.step).floor.toInt64.toInt
  Index.mk (q g.min.1) (q g.min.2) (q g.min.3)

def Grid.imax (g : Grid) : Index :=
  let q := fun (x : Float) => (x / g.step).ceil.toInt64.toInt
  Index.mk (q g.max.1) (q g.max.2) (q g.max.3)

def Grid.nextIndex? (g : Grid) (ijk : Index) : Option Index :=
  let i := ijk.1
  let j := ijk.2
  let k := ijk.3
  if k < g.imax.3 then
    some (Index.mk i j (k + 1))
  else
    if j < g.imax.2 then
      some (Index.mk i (j + 1) g.imin.3)
    else
      if i < g.imax.1 then
        some (Index.mk (i + 1) g.imin.2 g.imin.3)
      else
        none

partial def Grid.foldl {α} (f : α → Index → α) (init : α) (g : Grid) : α :=
  let rec foldAux (index? : Option Index) (current : α) : α :=
    match index? with
    | none => current
    | some index => foldAux (g.nextIndex? index) (f current index)
  foldAux (some g.imin) init

end STL

def Float.sign (f : Float) : Float :=
  if f ≥ 0 then 1.0 else -1.0

namespace STL

structure Edge where
  ijk1 : Index
  ijk2 : Index
  grid : Grid
deriving Repr

end STL

def Int.toFloat (i : Int) : Float :=
  if i < 0 then -(i.natAbs.toFloat) else i.natAbs.toFloat

namespace STL

def Grid.getElem (g : Grid) (ijk : Index) : Point :=
  let i := ijk.1
  let j := ijk.2
  let k := ijk.3
  Point.mk (g.step * i.toFloat) (g.step * j.toFloat) (g.step * k.toFloat)

instance : GetElem? Grid Index Point (fun _grid _index => True) where
  getElem (g : Grid) (ijk : Index) _ := g.getElem ijk
  getElem? (g : Grid) (ijk : Index)  := some (g.getElem ijk)

-- φ is a level-set function. Probably not the smartest test ATM (consider, 0+, 0-, etc)
def Edge.active (edge : Edge) (φ : Point → Float) : Bool :=
  (φ edge.grid[edge.ijk1]!).sign != (φ edge.grid[edge.ijk2]!).sign

-- TODO: probably should replace φ arg here by a general predicate and implement
-- filter on top of Grid.

def Grid.accActiveEdges (grid : Grid) (φ : Point → Float) (edges : List Edge) (ijk : Index) : List Edge :=
  let i := ijk.1
  let j := ijk.2
  let k := ijk.3
  let newEdges := [
    Edge.mk ijk (Index.mk i j (k+1)) grid,
    Edge.mk ijk (Index.mk i (j+1) k) grid,
    Edge.mk ijk (Index.mk (i+1) j k) grid,
  ]
  let newActiveEdges := newEdges.filter (fun edge => edge.active φ)
  newActiveEdges ++ edges

def Grid.activeEdges (grid : Grid) (φ : Point → Float) : List Edge :=
  grid.foldl (grid.accActiveEdges φ) []

#eval (
  let grid := Grid.mk (Point.mk (-2) (-2) (-2)) (Point.mk 2 2 2) (step := 0.5)
  let φ (p : Point) : Float := p.x * p.x + p.y * p.y + p.z * p.z - 1
  (grid.activeEdges φ).length

)


-- TODO: do not output a vector, this is much more spefic here,
-- use an enum ("cardinalDirection ?") that can be converted to a
-- unit vector.
def Edge.outerNormal (edge : Edge) (φ : Point → Float) : Vector :=
  let ijk1 := edge.ijk1
  let ijk2 := edge.ijk2
  let point_1 := edge.grid[ijk1]!
  let point_2 := edge.grid[ijk2]!
  let Δφ := φ point_2 - φ point_1
  if ijk1.1 ≠ ijk2.1 then
    if (ijk1.1 < ijk2.1 && Δφ > 0) || (ijk1.1 > ijk2.1 && Δφ < 0) then
      Vector.mk 1 0 0
    else
      Vector.mk (-1) 0 0
  else if ijk1.2 ≠ ijk2.2 then
    if (ijk1.2 < ijk2.2 && Δφ > 0) || (ijk1.2 > ijk2.2 && Δφ < 0) then
      Vector.mk 0 1 0
    else
      Vector.mk 0 (-1) 0
  else
    if (ijk1.3 < ijk2.3 && Δφ > 0) || (ijk1.3 > ijk2.3 && Δφ < 0) then
      Vector.mk 0 0 1
    else
      Vector.mk 0 0 (-1)

-- Same stuff here, φ is "too much" info, that could be better
def Grid.quadOfEdge (grid : Grid) (edge : Edge) (φ : Point → Float) : Quad :=
  let normal := edge.outerNormal φ
  let p1 := grid[edge.1]
  let p2 := grid[edge.2]
  let h := 0.5 * grid.step
  let p := weightedSum [(0.5, p1), (0.5, p2)]
  if normal == Vector.mk 0.0 0.0 1.0 then
    Quad.mk
      (p + (Vector.mk (-h) (-h) 0))
      (p + (Vector.mk ( h) (-h) 0))
      (p + (Vector.mk ( h) ( h) 0))
      (p + (Vector.mk (-h) ( h) 0))
  else if normal == Vector.mk 0 0 (-1) then
    Quad.mk
      (p + (Vector.mk (-h) ( h) 0))
      (p + (Vector.mk ( h) ( h) 0))
      (p + (Vector.mk ( h) (-h) 0))
      (p + (Vector.mk (-h) (-h) 0))
  else if normal == Vector.mk 0 1 0 then
    Quad.mk
      (p + (Vector.mk (-h) 0 (-h)))
      (p + (Vector.mk ( h) 0 (-h)))
      (p + (Vector.mk ( h) 0 ( h)))
      (p + (Vector.mk (-h) 0 ( h)))
  else if normal == Vector.mk 0 (-1) 0 then
    Quad.mk
      (p + (Vector.mk (-h) 0 ( h)))
      (p + (Vector.mk ( h) 0 ( h)))
      (p + (Vector.mk ( h) 0 (-h)))
      (p + (Vector.mk (-h) 0 (-h)))
  else if normal == Vector.mk 1 0 0 then
    Quad.mk
      (p + (Vector.mk (0) (-h) (-h)))
      (p + (Vector.mk (0) ( h) (-h)))
      (p + (Vector.mk (0) ( h) ( h)))
      (p + (Vector.mk (0) (-h) ( h)))
  else if normal == Vector.mk (-1) 0 0 then
    Quad.mk
      (p + (Vector.mk (0) (-h) ( h)))
      (p + (Vector.mk (0) ( h) ( h)))
      (p + (Vector.mk (0) ( h) (-h)))
      (p + (Vector.mk (0) (-h) (-h)))
  else
    panic! "unreachable"

def Grid.mesh (grid : Grid) (φ : Point → Float) : Mesh :=
  -- TODO: get all activeEdges, map to the normals, map to quads,
  -- maps to facets, collect in a mesh.
  let edges := grid.activeEdges φ
  let quads := edges.map (grid.quadOfEdge (φ := φ))
  let facets := quads.foldl
    (init := [])
    (fun facets quad => quad.split ++ facets)
  Mesh.mk facets


def test_sphere (step : Float): Mesh :=
  let grid := Grid.mk (Point.mk (-2) (-2) (-2)) (Point.mk 2 2 2) (step := step)
  let φ (p : Point) : Float := p.x * p.x + p.y * p.y + p.z * p.z - 1.0
  let mesh := grid.mesh φ
  mesh

end STL


def main := do
  let mesh := STL.test_sphere 0.1
  let stl := mesh.toSTL
  IO.FS.writeFile "sphere.stl" stl

def _main := do
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
