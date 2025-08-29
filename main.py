import sys

def main (args: list[str]):
  name = args[0]
  print(f"Hello {name}!", end=" ")
  if name == "Valérie":
    print("😘", end="")
  else:
    for _ in range(3):
      print("👋", end="")

if __name__ == "__main__":
  main(sys.argv[1:])