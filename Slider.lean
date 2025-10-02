import Raylib

def WIDTH := 32
def HEIGHT := 18
def SCALE := 25 -- 800 x 450 size (16:9 aspect ratio)

def main : IO Unit := do
  let mut x : Int := WIDTH / 2
  import_pyray
  init_window (WIDTH * SCALE) (HEIGHT * SCALE) "Slider"
  set_target_fps 10
  while not (<- window_should_close) do
    if (<- is_key_pressed KEY_LEFT) then
      x := max 0 (x - 1)
    else if (<- is_key_pressed KEY_RIGHT) then do
      x := min WIDTH (x + 1)
    begin_drawing
    clear_background WHITE
    draw_rectangle 0 0 (x * SCALE) (HEIGHT * SCALE) BLACK
    end_drawing
  close_window
