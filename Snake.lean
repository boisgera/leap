import Python

open Python (eval exec)

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

abbrev Point2 := Nat × Nat
abbrev Vector2 := Int × Int

def UP : Vector2 := (0, -1)
def DOWN : Vector2 := (0, 1)
def LEFT : Vector2 := (-1, 0)
def RIGHT : Vector2 := (1, 0)

structure GameState where
    snake_direction : Vector2
    snake_geometry : List Point2
    fruit : Point2

def WIDTH := 32
def HEIGHT := 18
def SCALE := 25 -- 800 x 450 size (16:9 aspect ratio)

def draw_grid : IO Unit := do
    for i in [0:HEIGHT] do
        for j in [0:WIDTH] do
            if (i + j) % 2 == 0 then
                draw_rectangle (j * SCALE) (i * SCALE) SCALE SCALE LIGHT_GREY

def draw_fruit (fruit : Point2) : IO Unit := do
    let (x, y) := fruit
    draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE STRAWBERRY

def draw (state : GameState) : IO Unit := do
    clear_background WHITE
    draw_grid
    draw_text "Hello Snake!" 190 200 20 VIOLET
    draw_fruit state.fruit
    for point in state.snake_geometry do
        let (x, y) := point
        draw_rectangle (x * SCALE) (y * SCALE) SCALE SCALE DARK_GREEN



def forward (state : GameState) : GameState :=
        let (dx, dy) := state.snake_direction
    let snake_geometry := state.snake_geometry
    let head := match state.snake_geometry.head? with
      | none => panic! "Snake geometry is empty"
      | some head => head
    let new_head : Point2 := (
        ((Int.ofNat head.1) + dx).toNat,
        ((Int.ofNat head.2) + dy).toNat,
    )
    let new_snake_geometry := new_head :: snake_geometry
    { state with snake_geometry := new_snake_geometry }

def trim (state : GameState) : GameState :=
    let snake_geometry := state.snake_geometry
    let new_snake_geometry := snake_geometry.take (snake_geometry.length - 1)
    { state with snake_geometry := new_snake_geometry }

def move (state : GameState) : GameState := Id.run do
    let mut state' <- forward state
    let mut head : Point2 := (0, 0)
    match state'.snake_geometry.head? with
      | none => pure ()
      | some head_ => head <- head_
    if not (head == state'.fruit) then
        state' := trim state'
    state'

def main : IO Unit := do
    import_ "pyray"
    init_window (WIDTH * SCALE) (HEIGHT * SCALE) "Snake Game"
    set_target_fps 10

    let mut state : GameState := {
        snake_direction : Int × Int := (1, 0),
        snake_geometry := [(15, 12), (16, 12), (17, 12)],
        fruit := (7, 7),
    }

    while not (<- window_should_close) do
        if (<- is_key_pressed KEY_UP) then do
            state := {state with snake_direction := UP}
        else if (<- is_key_pressed KEY_DOWN) then do
            state := {state with snake_direction := DOWN}
        else if (<- is_key_pressed KEY_LEFT) then do
            state := {state with snake_direction := LEFT}
        else if (<- is_key_pressed KEY_RIGHT) then do
            state := {state with snake_direction := RIGHT}

        state := move state
        begin_drawing
        draw state
        end_drawing

    close_window
