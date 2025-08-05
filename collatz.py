import sys

def collatz(x0, n):
    x = x0
    for _ in range(n):
        if x % 2 == 0:
            x = x // 2
        else:
            x = 3 * x + 1
    return x

if __name__ == "__main__":
    args = [int(arg) for arg in sys.argv[1:]]
    if len(args) == 2:
       print(collatz(args[0], args[1]))
    else:
       print("Usage: python collatz.py <x0> <n>")   
