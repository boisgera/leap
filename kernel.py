import ast
import os
import sys

def main(verbose=False):
    try:
        input = os.mkfifo("input")
    except FileExistsError:
        pass
    try:
       output = os.mkfifo("output")
    except FileExistsError:
        pass

    while True:
        with open("input", "r") as input_fifo:
            data = input_fifo.read()
        if data == "":
            if verbose:
                print("EOF")
            continue
        if verbose:
            print(f"<- {data}")
        try:
            ast.parse(data, mode="eval")
            out = eval(data, globals())
        except Exception:
            try:
                ast.parse(data, mode="exec")
                exec(data, globals())
                out = None
            except Exception as error:
                out = f"{type(error).__name__}: {error}"
        with open("output", "w") as output_fifo:
            output_fifo.write(repr(out))
            output_fifo.flush()
        if verbose:
            print(f"-> {repr(out)}")


if __name__ == "__main__":
    main(verbose = "-v" in sys.argv)
