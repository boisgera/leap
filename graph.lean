import Std
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

abbrev Point2 := Nat × Nat
abbrev Vector2 := Int × Int

def WIDTH := 32
def HEIGHT := 18
def SCALE := 25 -- 800 x 450 size (16:9 aspect ratio)

partial def getRandomPoints (count : Nat) (seed : Nat := 42) : List Point2 :=
  let rec loop (gen : StdGen) (n : Nat) (acc : List Point2) :=
    if n == 0 then
      acc.reverse
    else
      let (x, gen')  := randNat gen 0 WIDTH
      let (y, gen'') := randNat gen' 0 HEIGHT
      loop gen'' (n - 1) ((x, y) :: acc)
  loop (mkStdGen seed) count []

def blocks := (getRandomPoints 300 (seed := 42)).filter (fun (x, y) => (x, y) != (0, 0))

def Graph.ofBlocks (blocks : List Point2) : Graph := Id.run do
  let mut nodes : HashSet Node := {}
  let mut edges : HashSet Edge := {}
  for x in [0:WIDTH] do
    for y in [0:HEIGHT] do
      if !blocks.contains (x, y) then
        let node := (x, y)
        nodes <- nodes.insert node
        if x > 0 then
          let neighbor := (x - 1, y)
          if !blocks.contains neighbor then
            edges <- edges.insert (node, neighbor)
        if x < WIDTH - 1 then
          let neighbor := (x + 1, y)
          if !blocks.contains neighbor then
            edges <- edges.insert (node, neighbor)
        if y > 0 then
          let neighbor := (x, y - 1)
          if !blocks.contains neighbor then
            edges <- edges.insert (node, neighbor)
        if y < HEIGHT - 1 then
          let neighbor := (x, y + 1)
          if !blocks.contains neighbor then
            edges <- edges.insert (node, neighbor)
  return { nodes := nodes, edges := edges }


-- Interface to the Python Kernel
namespace Python

def eval (code : String) : IO String := do
    IO.FS.writeFile "input" code
    IO.FS.readFile "output"

def exec (code : String) : IO Unit := do
    let data <- eval code
    if data != "None" then
        panic! s!"Expected 'None' but got: {data}"

end Python

-- Python Bindings for raylib (mostly)
def import_ (module : String) : IO Unit := do
    -- IO.println "-"
    -- IO.println "--"
    Python.exec s!"from {module} import *"
    -- IO.println "---"

def init_window (width: Nat) (height: Nat) (title : String) : IO Unit := do
    Python.exec s!"init_window({width}, {height}, \"{title}\")"

def window_should_close : IO Bool := do
    let status <- Python.eval "window_should_close()"
    return status == "True"

def close_window : IO Unit := do
    Python.exec "close_window()"

def set_target_fps (fps : Nat) : IO Unit := do
    Python.exec s!"set_target_fps({fps})"

def begin_drawing : IO Unit := do
    Python.exec "begin_drawing()"

def end_drawing : IO Unit := do
    Python.exec "end_drawing()"

abbrev Color := Nat × Nat × Nat × Nat

def Color.to_string (color : Color) : String :=
    let (r, g, b, a) := color
    s!"({r}, {g}, {b}, {a})"

def clear_background (color : Color) : IO Unit := do
    Python.exec s!"clear_background({color.to_string})"


def draw_text (text : String) (x y : Nat) (fontSize : Nat) (color : Color) : IO Unit := do
    Python.exec s!"draw_text(\"{text}\", {x}, {y}, {fontSize}, {color.to_string})"

def draw_rectangle (x y : Nat) (width height : Nat) (color : Color) : IO Unit := do
    Python.exec s!"draw_rectangle({x}, {y}, {width}, {height}, {color.to_string})"


def KEY_UP := 265
def KEY_DOWN := 264
def KEY_LEFT := 263
def KEY_RIGHT := 262

def is_key_pressed (key : Nat) : IO Bool := do
    let status <- Python.eval s!"is_key_pressed({key})"
    return status == "True"

def is_key_down (key : Nat) : IO Bool := do
    let status <- Python.eval s!"is_key_down({key})"
    return status == "True"

def is_key_released (key : Nat) : IO Bool := do
    let status <- Python.eval s!"is_key_released({key})"
    return status == "True"

def is_key_up (key : Nat) : IO Bool := do
    let status <- Python.eval s!"is_key_up({key})"
    return status == "True"

def BLACK := (0, 0, 0, 255)
def WHITE := (255, 255, 255, 255)
def VIOLET := (135, 60, 190, 255)
def DARK_GREEN := (0, 109, 87, 255)
def LIGHT_GREY := (211, 211, 211, 255)
def STRAWBERRY := (215, 44, 22, 255)

def UP : Vector2 := (0, -1)
def DOWN : Vector2 := (0, 1)
def LEFT : Vector2 := (-1, 0)
def RIGHT : Vector2 := (1, 0)

--



def draw_grid : IO Unit := do
    for i in [0:HEIGHT] do
        for j in [0:WIDTH] do
            if (i + j) % 2 == 0 then
                draw_rectangle (j * SCALE) (i * SCALE) SCALE SCALE LIGHT_GREY


def main : IO Unit := do
    import_ "pyray"
    init_window (WIDTH * SCALE) (HEIGHT * SCALE) "Maze"

    set_target_fps 10

    while not (<- window_should_close) do
        begin_drawing
        clear_background WHITE
        for (x, y) in blocks do
            draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE BLACK
        end_drawing

    close_window
