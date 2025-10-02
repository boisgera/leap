
import Python

-- Python Bindings for raylib
def import_pyray : IO Unit := do
    Python.exec! "from pyray import *"

def init_window (width: Nat) (height: Nat) (title : String) : IO Unit := do
    Python.exec! "from pyray import *"
    Python.exec! s!"init_window({width}, {height}, \"{title}\")"

def window_should_close : IO Bool := do
    let status <- Python.eval! "window_should_close()"
    return status == "True"

def close_window : IO Unit := do
    Python.exec! "close_window()"

def set_target_fps (fps : Nat) : IO Unit := do
    Python.exec! s!"set_target_fps({fps})"

def begin_drawing : IO Unit := do
    Python.exec! "begin_drawing()"

def end_drawing : IO Unit := do
    Python.exec! "end_drawing()"

abbrev Color := Nat × Nat × Nat × Nat

def Color.to_string (color : Color) : String :=
    let (r, g, b, a) := color
    s!"({r}, {g}, {b}, {a})"

def clear_background (color : Color) : IO Unit := do
    Python.exec! s!"clear_background({color.to_string})"


def draw_text (text : String) (x y : Int) (fontSize : Int) (color : Color) : IO Unit := do
    Python.exec! s!"draw_text(\"{text}\", {x}, {y}, {fontSize}, {color.to_string})"

def draw_rectangle (x y : Int) (width height : Int) (color : Color) : IO Unit := do
    Python.exec! s!"draw_rectangle({x}, {y}, {width}, {height}, {color.to_string})"

def KEY_UP := 265
def KEY_DOWN := 264
def KEY_LEFT := 263
def KEY_RIGHT := 262

def is_key_pressed (key : Nat) : IO Bool := do
    let status <- Python.eval! s!"is_key_pressed({key})"
    return status == "True"

def is_key_down (key : Nat) : IO Bool := do
    let status <- Python.eval! s!"is_key_down({key})"
    return status == "True"

def is_key_released (key : Nat) : IO Bool := do
    let status <- Python.eval! s!"is_key_released({key})"
    return status == "True"

def is_key_up (key : Nat) : IO Bool := do
    let status <- Python.eval! s!"is_key_up({key})"
    return status == "True"

def BLACK := (0, 0, 0, 255)
def WHITE := (255, 255, 255, 255)
def VIOLET := (135, 60, 190, 255)
def DARK_GREEN := (0, 109, 87, 255)
def LIGHT_GREY := (211, 211, 211, 255)
def STRAWBERRY := (215, 44, 22, 255)
def ORANGE := (255, 165, 0, 255)

def UP : Int × Int := (0, -1)
def DOWN : Int × Int := (0, 1)
def LEFT : Int × Int := (-1, 0)
def RIGHT : Int × Int := (1, 0)
