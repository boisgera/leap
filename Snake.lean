import Raylib
import Python

abbrev Vector2 := Int × Int

structure GameState where
    snake_direction : Vector2
    snake_geometry : List Vector2
    fruit : Vector2

def WIDTH := 32
def HEIGHT := 18
def SCALE := 25 -- 800 x 450 size (16:9 aspect ratio)

def draw_grid : IO Unit := do
  for i in [0:HEIGHT] do
    for j in [0:WIDTH] do
      if (i + j) % 2 == 0 then
        draw_rectangle (j * SCALE) (i * SCALE) SCALE SCALE LIGHT_GREY

def draw_fruit (fruit : Vector2) : IO Unit := do
  let (x, y) := fruit
  draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE STRAWBERRY

def draw (state : GameState) : IO Unit := Python.batch do
  clear_background WHITE
  draw_grid
  draw_fruit state.fruit
  for point in state.snake_geometry do
    let (x, y) := point
    draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE DARK_GREEN

def snake_forward (state : GameState) : GameState :=
  let (dx, dy) := state.snake_direction
  let snake_geometry := state.snake_geometry
  let head := state.snake_geometry.head!
  let new_head := (
    (head.1 + dx) % WIDTH,
    (head.2 + dy) % HEIGHT,
  )
  let new_snake_geometry := new_head :: snake_geometry
{ state with snake_geometry := new_snake_geometry }

def snake_trim (state : GameState) : GameState :=
  let snake_geometry := state.snake_geometry
  let new_snake_geometry := snake_geometry.take (snake_geometry.length - 1)
  { state with snake_geometry := new_snake_geometry }

def snake_move (state : GameState) : GameState := Id.run do
  let mut state := snake_forward state
  let head := state.snake_geometry.head!
  if not (head == state.fruit) then
    state := snake_trim state
  return state

def handle_events (state : GameState) : IO GameState := do
  let mut state := state
  if (<- is_key_pressed KEY_UP) then do
    state := {state with snake_direction := UP}
  else if (<- is_key_pressed KEY_DOWN) then do
    state := {state with snake_direction := DOWN}
  else if (<- is_key_pressed KEY_LEFT) then do
    state := {state with snake_direction := LEFT}
  else if (<- is_key_pressed KEY_RIGHT) then do
    state := {state with snake_direction := RIGHT}
  return state

def main : IO Unit := do
  let mut state : GameState := {
    snake_direction := (1, 0),
    snake_geometry := [(15, 12), (16, 12), (17, 12)],
    fruit := (7, 7),
  }
  import_pyray
  init_window (WIDTH * SCALE) (HEIGHT * SCALE) "🐍 Snake Game"
  set_target_fps 10
  while not (<- window_should_close) do
    state <- handle_events state
    state := snake_move state
    begin_drawing
    draw state
    end_drawing

  close_window
