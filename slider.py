from pyray import (
    BLACK,
    KEY_LEFT,
    KEY_RIGHT,
    WHITE,
    begin_drawing,
    clear_background,
    close_window,
    draw_rectangle,
    end_drawing,
    init_window,
    is_key_pressed,
    set_target_fps,
    window_should_close,
)

WIDTH = 32
HEIGHT = 18
SCALE = 25  # 800 x 450 size (16:9 aspect ratio)


def main():
    x = WIDTH // 2
    init_window(WIDTH * SCALE, HEIGHT * SCALE, "Slider")
    set_target_fps(10)
    while not window_should_close():
        if is_key_pressed(KEY_LEFT):
            x = max(0, x - 1)
        elif is_key_pressed(KEY_RIGHT):
            x = min(WIDTH, x + 1)
        begin_drawing()
        clear_background(WHITE)
        draw_rectangle(0, 0, x * SCALE, HEIGHT * SCALE, BLACK)
        end_drawing()
    close_window()


if __name__ == "__main__":
    main()
