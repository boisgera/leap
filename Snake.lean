import Raylib

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
    -- draw_grid -- We'd rather not hammer the toupi server
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
        (((Int.ofNat head.1) + dx) % WIDTH).toNat,
        (((Int.ofNat head.2) + dy) % HEIGHT).toNat,
    )
    let new_snake_geometry := new_head :: snake_geometry
    { state with snake_geometry := new_snake_geometry }

def trim (state : GameState) : GameState :=
    let snake_geometry := state.snake_geometry
    let new_snake_geometry := snake_geometry.take (snake_geometry.length - 1)
    { state with snake_geometry := new_snake_geometry }

def move (state : GameState) : GameState := Id.run do
    let mut state := forward state
    let mut head : Point2 := (0, 0)
    match state.snake_geometry.head? with
      | none => pure ()
      | some head_ => head := head_
    if not (head == state.fruit) then
        state := trim state
    state

def main : IO Unit := do
    import_ "pyray"
    init_window (WIDTH * SCALE) (HEIGHT * SCALE) "Snake Game"

    -- set_target_fps 60

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
