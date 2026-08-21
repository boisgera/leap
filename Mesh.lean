import Lean
import Batteries.Lean.Float -- provides Float.toStringFull

namespace STL

/-!
Points and Vectors
--------------------------------------------------------------------------------
-/

instance : Hashable Float where
  hash f := hash f.toBits  -- or via UInt64 bit-reinterpretation

structure Point where
  x : Float := 0.0
  y : Float := 0.0
  z : Float := 0.0
deriving BEq, Hashable, Repr

structure Vector where
  x : Float := 0.0
  y : Float := 0.0
  z : Float := 0.0
deriving BEq, Hashable, Repr

def Vector.ex : Vector := { x := 1.0 }

def Vector.ey : Vector := { y := 1.0 }

def Vector.ez : Vector := { z := 1.0 }

#eval Vector.mk 1.0 2.0 3.0
-- { x := 1.000000, y := 2.000000, z := 3.000000 }

#eval Float.toString (0.1 + 0.2)
-- "0.300000"

#eval Float.toStringFull (0.1 + 0.2)
-- "0.3000000000000000444089209850062616169452667236328125"

#eval Float.toStringFull ((2.0 ^ 10.0) + 0.1)
-- "0.3000000000000000444089209850062616169452667236328125"

#eval Float.toStringFull 0.0
-- 0

#eval Float.toStringFull (1.0 / 0.0)
-- "inf"

#eval Float.toStringFull (-1.0 / 0.0)
-- "-inf"

#eval Float.toStringFull (-0.0)
-- 0

#eval Float.toStringFull (0.0 / 0.0)
-- "NaN"

def Vector.origin := Vector.mk 0 0 0

instance : Inhabited Vector where
  default := Vector.origin

def Vector.toSTL (u : Vector) : String :=
  s!"{u.1.toStringFull} {u.2.toStringFull} {u.3.toStringFull}"


def Vector.add (u v : Vector) : Vector :=
  {
    x := u.x + v.x,
    y := u.y + v.y,
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


def Vector.neg (u : Vector) : Vector := (-1.0) • u

instance : Neg Vector where
  neg := Vector.neg   -- proof obligations if MyType has invariants

def Vector.sub (u v : Vector) : Vector :=
  u + (-v)

instance : Sub Vector where
  sub := Vector.sub


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

/-!
Facets, Quads and Meshes
--------------------------------------------------------------------------------
-/

structure Facet where
  vertex_1 : Point -- The f.1 notation is for free
  vertex_2 : Point
  vertex_3 : Point
deriving BEq, Hashable, Repr

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

-- not sure we need a new type here... Actually the namespace is good,
-- to host the `split` method.
structure Quad where
  vertex_1 : Point
  vertex_2 : Point
  vertex_3 : Point
  vertex_4 : Point
deriving BEq, Hashable, Inhabited, Repr

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
  name? : Option String := none
deriving BEq, Hashable, Repr

/-!
ToSTL type class
--------------------------------------------------------------------------------
-/

class ToSTL.{u} (α : Type u) where
  toSTL : α → String

def Facet.toSTL (f : Facet) : String :=
s!"facet normal {f.normal.toSTL}
    outer loop
        vertex {f.1.toSTL}
        vertex {f.2.toSTL}
        vertex {f.3.toSTL}
    endloop
endfacet"

instance : ToSTL Facet where
  toSTL := Facet.toSTL

def Mesh.toSTL (m : Mesh) : String :=
  let name := if let some name := m.name? then name else ""
  let facetsSTL := m.facets |>.map ToSTL.toSTL |> String.intercalate "\n"
  s!"solid {name}\n{facetsSTL}\nendsolid {name}"

instance : ToSTL Mesh where
  toSTL := Mesh.toSTL

def test_facet :=
  let mesh : Mesh := {
    facets := [
      Facet.mk (Point.mk 0 0 0) (Point.mk 1 0 0) (Point.mk 0 1 0)
    ]
  }
  IO.println mesh.toSTL

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
  let mesh : Mesh := { facets, name? := "cube"}
  let meshSTL := mesh |> ToSTL.toSTL
  IO.println meshSTL
  IO.FS.writeFile "cube.stl" meshSTL

-- #eval test_cube

-- TODO:
-- given a SDF and a quantized 3D range, get the active edges (with sign change)
-- collect the corresponding quad and build the mesh.
-- How do we deal with the fact that we don't want to have all (active and non
-- active) edges in memory at the same time? Try a first version where we don't
-- care? T


/-!
Tesselation
--------------------------------------------------------------------------------
-/

structure Index where
  i : Int
  j : Int
  k : Int
deriving BEq, Hashable, Repr

def Index.le (ijk1 ijk2 : Index) : Bool :=
  ijk1.1 ≤ ijk2.1 && ijk1.2 ≤ ijk2.2 && ijk1.3 ≤ ijk2.3

structure Grid where
  imin : Index
  imax : Index
  scale : Float
deriving BEq, Hashable, Repr

def Grid.contains (grid : Grid) (ijk : Index) : Bool :=
  Index.le grid.imin ijk && Index.le ijk grid.imax

def Grid.getElem (grid : Grid) (ijk : Index) : Point :=
  let ⟨i, j, k⟩ := ijk
  let scale := grid.scale
  {
    x := Float.ofInt i * scale,
    y := Float.ofInt j * scale,
    z := Float.ofInt k * scale,
  }

-- For the sake if simplicity, we provide a point grid[ijk]
-- even if ijk is out of the grid.
instance : GetElem? Grid Index Point (fun _grid _index => True) where
  getElem (g : Grid) (ijk : Index) _ := g.getElem ijk
  getElem? (g : Grid) (ijk : Index)  := some (g.getElem ijk)

def Grid.min (grid : Grid) : Point := grid[grid.imin]

def Grid.max (grid : Grid) : Point := grid[grid.imax]

def Grid.nextIndex? (g : Grid) (ijk : Index) : Option Index :=
  let ⟨i, j, k⟩ := ijk
  if k < g.imax.3 then
    some { i, j, k := k + 1 }
  else if j < g.imax.2 then -- reset k and increase j
    some { i, j := j + 1, k := g.imin.3 }
  else if i < g.imax.1 then -- reset j and k, increase i
    some { i := i + 1, j := g.imin.2, k := g.imin.3 }
  else -- that's over!
    none

partial def Grid.foldl {α} (f : α → Index → α) (init : α) (grid : Grid) : α :=
  let rec foldAux (index? : Option Index) (current : α) : α :=
    match index? with
    | none => current
    | some index => foldAux (grid.nextIndex? index) (f current index)
  foldAux (some grid.imin) init

inductive Axis where
  | x
  | y
  | z
  deriving BEq, Hashable, Repr

def Axis.succ : Axis → Index → Index
  | x => fun ⟨i, j, k⟩ => ⟨i + 1, j    , k    ⟩
  | y => fun ⟨i, j, k⟩ => ⟨i    , j + 1, k    ⟩
  | z => fun ⟨i, j, k⟩ => ⟨i    , j    , k + 1⟩

structure Edge where
  ijk : Index
  axis : Axis
deriving BEq, Hashable, Repr

def Edge.indices (edge : Edge) : Index × Index :=
  match edge with
  | { ijk, axis, .. } => (ijk, axis.succ ijk)

-- Belongs to edge or to grid?
def Edge.active (edge : Edge) (grid : Grid) (φ : Point → Float) : Bool :=
  let (ijk1, ijk2) := edge.indices
  let p1 := grid[ijk1]
  let p2 := grid[ijk2]
  φ p1 < 0 && 0 ≤ φ p2 || φ p2 < 0 && 0 ≤ φ p1

-- TODO: probably should replace φ arg here by a general predicate and implement
-- filter on top of Grid (?)
def Grid.activeEdgesAux (grid : Grid) (φ : Point → Float) (edges : List Edge) (ijk : Index) : List Edge :=
  let newEdges := [ -- we're lucky that we go overboard on the grid here ...
  -- we should actually check the values of ijk and filter accordingly
    { ijk, axis := .x },
    { ijk, axis := .y },
    { ijk, axis := .z },
  ]
  let newActiveEdges := newEdges.filter (fun edge => edge.active grid φ)
  newActiveEdges ++ edges

def Grid.activeEdges (grid : Grid) (φ : Point → Float) : List Edge :=
  grid.foldl (grid.activeEdgesAux φ) []

-- def crossing (p1 p2 : Point) (d1 d2 : Float) : Point :=
--   if d1 == d2 then
--     weightedSum [(1.0, p1), (1.0, p2)]
--   else
--     let w1 := d2 / (d2 - d1)
--     let w2 := -d1 / (d2 - d1)
--     weightedSum [(w1, p1), (w2, p2)]

-- def Grid.accCrossingPoints (grid : Grid) (φ : Point → Float) (edges : Std.HashMap Edge Point) (ijk : Index) : List Edge :=
--   let i := ijk.1
--   let j := ijk.2
--   let k := ijk.3
--   let newEdges := [ -- we're lucky that we go overboard on the grid here
--     Edge.mk ijk (Index.mk i j (k+1)) grid,
--     Edge.mk ijk (Index.mk i (j+1) k) grid,
--     Edge.mk ijk (Index.mk (i+1) j k) grid,
--   ]
--   let newActiveEdges := newEdges.filter (fun edge => edge.active φ)
--   newActiveEdges ++ edges

-- def Grid.crossingPoints (grid : Grid) (φ : Point → Float) :
--     Std.HashMap Edge Point :=
--   grid.foldl () {}


-- TODO: better structure here instead of List Edge? Hashset?
-- Alternatively, return the crossint point in a Hashmap (for surface nets)

#eval (
  let grid : Grid := { imin := ⟨-4, -4, -4⟩, imax := ⟨4, 4, 4⟩, scale := 0.5 }
  let φ (p : Point) : Float := p.x * p.x + p.y * p.y + p.z * p.z - 1
  (grid.activeEdges φ).length

)


-- TODO: do not output a vector, this is much more specific here,
-- use an enum ("cardinalDirection ?") that can be converted to a
-- unit vector.
-- So that later we can pattern match
def Edge.outerNormal (grid : Grid) (edge : Edge) (φ : Point → Float) : Vector :=
  let (ijk1, ijk2) := edge.indices
  let ⟨i1, j1, k1⟩ := ijk1
  let ⟨i2, j2, k2⟩ := ijk2
  let p1 := grid[ijk1]
  let p2 := grid[ijk2]
  let Δφ := φ p2 - φ p1
  if i1 ≠ i2 then
    if (i1 < i2 && Δφ > 0) || (i1 > i2 && Δφ < 0) then
      { x := 1 }
    else
      { x := -1 }
  else if j1 ≠ j2 then
    if (j1 < j2 && Δφ > 0) || (j1 > j2 && Δφ < 0) then
      { y := 1 }
    else
      { y := -1 }
  else
    if (k1 < k2 && Δφ > 0) || (k1 > k2 && Δφ < 0) then
      { z := 1 }
    else
      { z := -1}

-- TODO: to have surface nets, we need a (hash?)map from "cell" to weighted
-- center, which requires already to have a set of active edges.

-- Same stuff here, φ is "too much" info, that could be better
def Grid.quadOfEdge (grid : Grid) (edge : Edge) (φ : Point → Float) : Quad :=
  let normal := edge.outerNormal grid φ
  let (ijk1, ijk2) := edge.indices
  let p1 := grid[ijk1]
  let p2 := grid[ijk2]
  let h := 0.5 * grid.scale
  let p := weightedSum [(0.5, p1), (0.5, p2)]
  open _root_.STL.Vector in
  if normal == { z := 1 } then
    Quad.mk
      (p + h • (- ex - ey))
      (p + h • (  ex - ey))
      (p + h • (  ex + ey))
      (p + h • (- ex + ey))
  else if normal == { z := -1 } then -- TODO: refactor, this is the reverse
    Quad.mk
      (p + h • (- ex + ey))
      (p + h • (  ex + ey))
      (p + h • (  ex - ey))
      (p + h • (- ex - ey))
  else if normal == { y := -1 } then
    Quad.mk
      (p + h • (- ex - ez))
      (p + h • (  ex - ez))
      (p + h • (  ex + ez))
      (p + h • (- ex + ez))
  else if normal == { y := 1 } then
    Quad.mk
      (p + h • (- ex + ez))
      (p + h • (  ex + ez))
      (p + h • (  ex - ez))
      (p + h • (- ex - ez))
  else if normal == { x := -1 } then
    Quad.mk
      (p + h • (- ey + ez))
      (p + h • (  ey + ez))
      (p + h • (  ey - ez))
      (p + h • (- ey - ez))
  else if normal == { x := 1 } then
    Quad.mk
      (p + h • (- ey - ez))
      (p + h • (  ey - ez))
      (p + h • (  ey + ez))
      (p + h • (- ey + ez))
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
  { facets }


def test_sphere : Mesh :=
  let grid : Grid := {
    imin := ⟨-25, -25, -25⟩,
    imax := ⟨ 25,  25,  25⟩,
    scale := 0.05
  }
  let φ (p : Point) : Float := p.x * p.x + p.y * p.y + p.z * p.z - 1.0
  let mesh := grid.mesh φ
  mesh

end STL

def main := do
  let mesh := STL.test_sphere
  let stl := mesh.toSTL
  IO.FS.writeFile "sphere.stl" stl

-- #eval main

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
