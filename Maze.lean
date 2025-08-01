import Std

import Raylib

open Std (HashSet)

abbrev Node := Nat × Nat

abbrev Edge := Node × Node

abbrev Path := List Node

instance : Repr Edge where
  reprPrec e _ :=
    Std.Format.text s!"{e.1} --- {e.2}"

instance : Repr Path where
  reprPrec p _ :=
    Std.Format.text s!"[{String.intercalate " -> " (List.map reprStr p)}]"

def p : Path := [(1, 2), (2, 3), (3, 4)]

structure Graph where
  nodes : HashSet Node
  edges : HashSet Edge
deriving Repr


def Std.HashSet.choose! (s : HashSet Node) : Node :=
  match s.toList with
  | [] => panic! "HashSet.choose! called on an empty set"
  | x::_ => x

def Graph.neighbors (graph : Graph) (node : Node) : List Node := Id.run do
  let mut neighbors : List Node := []
  for edge in graph.edges do
    if edge.1 == node then
      neighbors := edge.2 :: neighbors
    else if edge.2 == node then
      neighbors := edge.1 :: neighbors
  return neighbors

def Graph.reachable_set (graph : Graph) (src : Node) : HashSet Node := Id.run do
  let mut todo : HashSet Node := { src }
  let mut done : HashSet Node := {}
  while !todo.isEmpty do
    let current := todo.choose!
    todo := todo.erase current
    for neighbor in graph.neighbors current do
      if !done.contains neighbor then
        todo := todo.insert neighbor
    done := done.insert current
  return done

instance {α : Type} [BEq α] [Hashable α] : BEq (HashSet α) where
  beq s₁ s₂ := s₁.toArray == s₂.toArray

-- reachable_state : (todo, done) (could be a structure instead...)
abbrev ReachableState := (HashSet Node) × (HashSet Node)

def Graph.reachable_step (graph : Graph) (state: ReachableState) : ReachableState :=
  let (todo, done) := state
  if todo.isEmpty then
    state
  else
    let current := todo.choose!
    let todo := todo.erase current
    let neighbors := graph.neighbors current
    let f := fun acc neighbor =>
      if done.contains neighbor then
        acc
      else
        acc.insert neighbor
    let todo := neighbors.foldl f todo
    let done := done.insert current
    (todo, done)

partial def Graph.reachable_fixpoint (graph : Graph) (state : ReachableState) : ReachableState :=
  let next_state := graph.reachable_step state
  if next_state == state then
    state
  else
    reachable_fixpoint graph next_state

def WIDTH := 16 -- 32
def HEIGHT := 9 -- 18
def SCALE := 50-- 25 -- 800 x 450 size (16:9 aspect ratio)

partial def getRandomPoints (count : Nat) (seed : Nat := 0) : List Point2 :=
  let rec loop (gen : StdGen) (n : Nat) (acc : List Point2) :=
    if n == 0 then
      acc.reverse
    else
      let (x, gen')  := randNat gen 0 WIDTH
      let (y, gen'') := randNat gen' 0 HEIGHT
      loop gen'' (n - 1) ((x, y) :: acc)
  loop (mkStdGen seed) count []

def blocks := (getRandomPoints 100  (seed := 1) ).filter (fun (x, y) => (x, y) != (0, 0))

def Graph.ofBlocks (blocks : List Point2) : Graph := Id.run do
  let mut nodes : HashSet Node := {}
  let mut edges : HashSet Edge := {}
  for y in [0:HEIGHT] do
    for x in [0:WIDTH] do
      if !blocks.contains (x, y) then
        nodes := nodes.insert (x, y)
        let xi := x |> Int.ofNat
        let yi := y |> Int.ofNat
        for (dx, dy) in [(-1, 0), (1, 0), (0, -1), (0, 1)] do
          let neighbor : Point2 :=
            (
              xi |> (· + dx) |> (· % Int.ofNat WIDTH)  |> Int.toNat,
              yi |> (· + dy) |> (· % Int.ofNat HEIGHT) |> Int.toNat
            )
          if !blocks.contains neighbor then
            edges := edges.insert ((x, y), neighbor)
  return { nodes := nodes, edges := edges }

def draw_grid : IO Unit := do
    for i in [0:HEIGHT] do
        for j in [0:WIDTH] do
            if (i + j) % 2 == 0 then
                draw_rectangle (j * SCALE) (i * SCALE) SCALE SCALE LIGHT_GREY


def main : IO Unit := do
    import_ "pyray"
    init_window (WIDTH * SCALE) (HEIGHT * SCALE) "Maze"

    let graph := Graph.ofBlocks blocks
    let origin : Point2 := (0, 0)
    let mut todo : HashSet Node := { origin }
    let mut done : HashSet Node := {}

    -- IO.println s!"Edges: {graph.edges.toList}"
    IO.println s!"Reachable nodes: {done.toList.length}"
    IO.println s!"Blocks: {blocks.length}"

    set_target_fps 1

    while not (<- window_should_close) do
        begin_drawing
        clear_background WHITE
        for (x, y) in blocks do
          draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE BLACK
        for (x, y) in todo do
          draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE ORANGE
        for (x, y) in done do
          draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE STRAWBERRY
        end_drawing

        (todo, done) := graph.reachable_step (todo, done)
    close_window
