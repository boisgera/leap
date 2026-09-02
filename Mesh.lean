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

def Quad.split (quad : Quad) : List Facet :=
  let center := quad.toList.map (fun p => (0.25, p)) |> weightedSum
  [
    Facet.mk quad.1 quad.2 center,
    Facet.mk quad.2 quad.3 center,
    Facet.mk quad.3 quad.4 center,
    Facet.mk quad.4 quad.1 center,
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

-- Alternate constructor: the smallest `Grid` (at the given `scale`)
-- whose extent covers the box between `min` and `max`.
def Grid.ofBounds (min max : Point) (scale : Float) : Grid :=
  let floorIndex (p : Point) : Index :=
    { i := (p.x / scale).floor.toInt64.toInt,
      j := (p.y / scale).floor.toInt64.toInt,
      k := (p.z / scale).floor.toInt64.toInt }
  let ceilIndex (p : Point) : Index :=
    { i := (p.x / scale).ceil.toInt64.toInt,
      j := (p.y / scale).ceil.toInt64.toInt,
      k := (p.z / scale).ceil.toInt64.toInt }
  { imin := floorIndex min, imax := ceilIndex max, scale }

#eval Grid.ofBounds (Point.mk (-1) (-1) (-1)) (Point.mk 1 1 1) 0.3
-- expect imin ≈ ⟨-4,-4,-4⟩ (since -1/0.3 ≈ -3.33, floor = -4),
--        imax ≈ ⟨4,4,4⟩   (since  1/0.3 ≈  3.33, ceil  =  4)

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

-- Unordered edge between neighbours
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

def crossing (p1 p2 : Point) (d1 d2 : Float) : Point :=
  if d1 == d2 then
    weightedSum [(0.5, p1), (0.5, p2)] -- (semi-)junk value
  else
    let w1 := d2 / (d2 - d1)
    let w2 := -d1 / (d2 - d1)
    weightedSum [(w1, p1), (w2, p2)]

def Grid.crossingPointsAux
    (grid : Grid) (φ : Point → Float) (crossingPoints : Std.HashMap Edge Point) (ijk : Index)
    : Std.HashMap Edge Point :=
  let i := ijk.1
  let j := ijk.2
  let k := ijk.3
  let newEdges : List Edge := [ -- we're lucky that we go overboard on the grid here
    { ijk, axis := .x },
    { ijk, axis := .y },
    { ijk, axis := .z },
  ]
  let newActiveEdges := newEdges.filter
    fun edge => edge.active (grid := grid) (φ := φ)
  let newCrossingPoints : List (Edge × Point) := newActiveEdges.map
    fun edge =>
      let (ijk1, ijk2) := edge.indices
      let p1 := grid[ijk1]
      let p2 := grid[ijk2]
      let d1 := φ p1
      let d2 := φ p2
      let cross := crossing p1 p2 d1 d2
      (edge, cross)
  newCrossingPoints.foldl
    (fun acc (edge, cross) => acc.insert edge cross)
    crossingPoints

def Grid.crossingPoints (grid : Grid) (φ : Point → Float) : Std.HashMap Edge Point :=
  grid.foldl (Grid.crossingPointsAux grid φ) {}

def Grid.computeCenter (grid : Grid) (crossingPoints : Std.HashMap Edge Point) (ijk : Index)
    : Point :=
  let edges : List Edge := [
    { ijk, axis := .x },
    { ijk, axis := .y },
    { ijk, axis := .z },
    { ijk := Axis.x.succ ijk, axis := .y },
    { ijk := Axis.x.succ ijk, axis := .z },
    { ijk := Axis.y.succ ijk, axis := .x },
    { ijk := Axis.y.succ ijk, axis := .z },
    { ijk := Axis.z.succ ijk, axis := .x },
    { ijk := Axis.z.succ ijk, axis := .y },
    { ijk := Axis.x.succ (Axis.y.succ ijk), axis := .z },
    { ijk := Axis.x.succ (Axis.z.succ ijk), axis := .y },
    { ijk := Axis.y.succ (Axis.z.succ ijk), axis := .x },
  ]
  let points := edges.filterMap (fun k => crossingPoints.get? k)
  let n := points.length
  if n = 0 then
    let min := grid[ijk]
    let ⟨i, j, k⟩ := ijk
    let max := grid[{ i := i + 1, j := j + 1, k := k + 1 : Index }]
    weightedSum [(0.5, min), (0.5, max)]
  else
    let weightedPoints := points.map (fun point => (1 / n.toFloat, point))
    weightedSum weightedPoints

-- TODO: do not output a vector, this is much more specific here,
-- use an enum ("cardinalDirection ?") that can be converted to a
-- unit vector.
-- So that later we can pattern match
-- Mmm and the name outerNormal, I get it, but it kinda sucks...
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
      { z := -1 }

def Grid.quadOfEdge'
  (grid : Grid) (edge : Edge) (φ : Point → Float)
  (crossingPoints : Std.HashMap Edge Point) : Quad :=
  let ⟨⟨i,j,k⟩, axis⟩ := edge
  let cells : List Index := match axis with
    | .x => [
        { i, j := j - 1, k := k - 1 },
        { i, j := j    , k := k - 1 },
        { i, j := j    , k := k     },
        { i, j := j - 1, k := k     },
      ]
    | .y => [
        { i := i - 1, j, k := k - 1 },
        { i := i    , j, k := k - 1 },
        { i := i    , j, k := k     },
        { i := i - 1, j, k := k     },
      ]
    | .z => [
        { i := i - 1, j := j - 1, k },
        { i := i    , j := j - 1, k },
        { i := i    , j := j    , k },
        { i := i - 1, j := j    , k },
      ]
  -- `cells` above is wound so that, as-is, it produces an outward
  -- normal of +x (for .x edges), -y (for .y edges) or +z (for .z
  -- edges) -- the sign flips for .y because of the handedness of the
  -- cross product across the three axes (same asymmetry visible in
  -- Grid.quadOfEdge's separate x/z vs y quad-vertex tables). Reverse
  -- the winding whenever that doesn't match the actual φ-gradient
  -- outward direction, so the mesh normal is consistent with the
  -- voxel renderer's.
  let defaultIsPositive := match axis with
    | .x => true
    | .y => false
    | .z => true
  let outward := edge.outerNormal grid φ
  let outwardIsPositive := match axis with
    | .x => outward.x > 0
    | .y => outward.y > 0
    | .z => outward.z > 0
  let orderedCells := if outwardIsPositive == defaultIsPositive then cells else cells.reverse
  let points := orderedCells.map
    fun cell =>
      grid.computeCenter (ijk := cell) (crossingPoints := crossingPoints)
  Quad.mk points[0]! points[1]! points[2]! points[3]!

#eval (
  let grid : Grid := { imin := ⟨-4, -4, -4⟩, imax := ⟨4, 4, 4⟩, scale := 0.5 }
  let φ (p : Point) : Float := p.x * p.x + p.y * p.y + p.z * p.z - 1
  (grid.activeEdges φ).length

)


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

def Grid.voxelMesh (grid : Grid) (φ : Point → Float) : Mesh :=
  -- TODO: get all activeEdges, map to the normals, map to quads,
  -- maps to facets, collect in a mesh.
  let edges := grid.activeEdges φ
  let quads := edges.map (grid.quadOfEdge (φ := φ))
  let facets := quads.foldl
    (init := [])
    (fun facets quad => quad.split ++ facets)
  { facets }

def Grid.surfaceNetMesh (grid : Grid) (φ : Point → Float) : Mesh :=
  let crossingPoints := grid.crossingPoints φ
  let edges := crossingPoints.keys
  let quads := edges.map (fun edge => grid.quadOfEdge' edge φ crossingPoints)
  let facets := quads.foldl
    (init := [])
    (fun facets quad => quad.split ++ facets)
  { facets }


/-!
Sparse (KDTree) Iteration
--------------------------------------------------------------------------------
-/

def Grid.split (grid : Grid) : Grid × Grid :=
  let di := grid.imax.i - grid.imin.i
  let dj := grid.imax.j - grid.imin.j
  let dk := grid.imax.k - grid.imin.k
  if dk ≥ dj && dk ≥ di then
    let kmid := (grid.imin.k + grid.imax.k) / 2
    (
      { grid with imax := ⟨grid.imax.i, grid.imax.j, kmid⟩ },
      { grid with imin := ⟨grid.imin.i, grid.imin.j, kmid⟩ }
    )
  else if dj ≥ di then
    let jmid := (grid.imin.j + grid.imax.j) / 2
    (
      { grid with imax := ⟨grid.imax.i, jmid, grid.imax.k⟩ },
      { grid with imin := ⟨grid.imin.i, jmid, grid.imin.k⟩ }
    )
  else
    let imid := (grid.imin.i + grid.imax.i) / 2
    (
      { grid with imax := ⟨imid, grid.imax.j, grid.imax.k⟩ },
      { grid with imin := ⟨imid, grid.imin.j, grid.imin.k⟩ }
    )

partial def Grid.crossingPointsSparse (grid : Grid)
    (φ : Point → Float) (crossingPoints : Std.HashMap Edge Point := {}) :
    Std.HashMap Edge Point :=
    let d := φ grid[grid.imin]
    let delta_square : Int := (
      (grid.imax.i - grid.imin.i) ^ 2 +
      (grid.imax.j - grid.imin.j) ^ 2 +
      (grid.imax.k - grid.imin.k) ^ 2
    )
    if d ^ 2 > (grid.scale ^ 2 * Float.ofInt delta_square) then
      crossingPoints
    else if (
      (grid.imax.i - grid.imin.i) == 1 &&
      (grid.imax.j - grid.imin.j) == 1 &&
      (grid.imax.k - grid.imin.k) == 1 )
    then
      grid.crossingPointsAux φ crossingPoints (ijk := grid.imin)
    else
      let (grid1, grid2) := grid.split
      let crossingPoints1 := grid1.crossingPointsSparse φ crossingPoints
      let crossingPoints2 := grid2.crossingPointsSparse φ crossingPoints1
      crossingPoints2

#eval (
  let grid : Grid := { imin := ⟨-4, -4, -4⟩, imax := ⟨4, 4, 4⟩, scale := 0.5 }
  let φ (p : Point) : Float := ‖p - Point.origin‖ - 1
  ((grid.crossingPointsSparse φ).size, (grid.crossingPoints φ).size)
)
-- expect a matching pair, e.g. (n, n)

#eval (
  let grid : Grid := { imin := ⟨-8, -2, -2⟩, imax := ⟨8, 2, 2⟩, scale := 0.5 }
  let φ (p : Point) : Float := ‖p - Point.origin‖ - 1
  ((grid.crossingPointsSparse φ).size, (grid.crossingPoints φ).size)
)
-- exercises the (fixed) i-axis branch of Grid.split; expect a matching pair

def Grid.surfaceNetMeshSparse (grid : Grid) (φ : Point → Float) : Mesh :=
  let crossingPoints := grid.crossingPointsSparse φ
  let edges := crossingPoints.keys
  let quads := edges.map (fun edge => grid.quadOfEdge' edge φ crossingPoints)
  let facets := quads.foldl
    (init := [])
    (fun facets quad => quad.split ++ facets)
  { facets }

/-!
--------------------------------------------------------------------------------
-/

def testVoxelSphere (scale : Float := 1.0) : Mesh :=
  let grid : Grid := Grid.ofBounds
    ⟨ -1.0, -1.0, -1.0 ⟩
    ⟨  1.0,  1.0,  1.0 ⟩
    scale
  let φ (p : Point) : Float := ‖p - Point.origin‖ - 1.0
  let mesh := grid.voxelMesh φ
  mesh

def testSurfaceNetSphere (scale : Float := 1.0) : Mesh :=
  let grid : Grid := Grid.ofBounds
    ⟨ -1.0, -1.0, -1.0 ⟩
    ⟨  1.0,  1.0,  1.0 ⟩
    scale
  let φ (p : Point) : Float := ‖p - Point.origin‖ - 1.0
  let mesh := grid.surfaceNetMesh φ
  mesh

def testSurfaceNetSphereSparse (scale : Float := 1.0) : Mesh :=
  let grid : Grid := Grid.ofBounds
    ⟨ -1.0, -1.0, -1.0 ⟩
    ⟨  1.0,  1.0,  1.0 ⟩
    scale
  let φ (p : Point) : Float := ‖p - Point.origin‖ - 1.0
  let mesh := grid.surfaceNetMeshSparse φ
  mesh

end STL

def main := do
  let scale : Float := 2 ^ (-2) -- 2 ^ (-5)
  let voxelMesh := STL.testVoxelSphere scale
  voxelMesh.toSTL |> IO.FS.writeFile "sphere-voxel.stl"
  IO.println "*"
  let surfaceNetMesh := STL.testSurfaceNetSphere scale
  surfaceNetMesh.toSTL |> IO.FS.writeFile "sphere-surface-net.stl"
  IO.println "**"
  let surfaceNetMeshSparse := STL.testSurfaceNetSphereSparse scale
  surfaceNetMeshSparse.toSTL |> IO.FS.writeFile "sphere-surface-net-sparse.stl"
  IO.println "***"

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
