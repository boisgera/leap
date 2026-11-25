
/-!

Preamble
--------------------------------------------------------------------------------

  - [ ] Learn the basics about [Brainfuck], its syntax, data and execution.

  - [ ] Create a top-level `Brainfuck` namespace and child namespaces
    `V1`, `V2` and `V3` version namespaces.

[Brainfuck]: https://en.wikipedia.org/wiki/Brainfuck



Version 1 : Data
--------------------------------------------------------------------------------

In this section, everything takes place in `V1` (the root namespace).

### Data structure

  - [ ] Create a new `Data` structure that represents the tape and the data
    pointer.

  - [ ] Implement `Data` methods `incr`, `decr`, `left` and `right`
    with a common `Data → Data` signature which correspond to the
    `+`, `-`, `<` and `>` instructions.

  - [ ] Create a `Data` method `toString` that represent cell values in
    hexadecimal and adds a bracket around the cell which is pointed to.
    For example, you could associates to the tape with cells values
    0, 255, 127 and 255 and with a pointer to the third cell like:

    ```
    00 ff [7f] ff
    ```

  - [ ] With `DataM` an alias for `StateM Data`, implement variants of the
    `incr`, `decr`, `left` and `right` in the root namespace
    with type `DataM Unit`.


### Program execution

  - [ ] Define a new `Command` type with constructors `incr`, `decr`,
    `left` and `right` (with no arguments).

  - [ ] Define a `Command.exec` method of type `Command → DataM Unit`
    that executes a single command.

  - [ ] Define `Program` as a structure that contains a `commands` field of
    type `List Command`, then implement `Program.exec` which executes
    a list of commands.

### Parser

  - [ ] Define a `parse` function that turns a `String` that represents
    the content of a Brainfuck program into a `Program`.

### Command-line interface

  - [ ] Define a `main` function that reads the filename of a Brainfuck program,
    parses it, executes it and display the tape at the end of the execution.

-/

namespace V1

structure Data where
  tape : List UInt8 := [0] -- reversed
  index : Nat := 0         -- *not* reversed (convenient to be ≥ 0)

partial def Data.incr (data : Data) : Data :=
  match data.tape with
  | head :: tail =>
    if data.index = data.tape.length - 1 then
      { data with tape := (head + 1) :: tail }
    else
      Data.incr { data with tape := tail }
  | [] => data -- unreachable code, return junk

partial def Data.decr (data : Data) : Data :=
  match data.tape with
  | head :: tail =>
    if data.index = data.tape.length - 1 then
      { data with tape := (head - 1) :: tail }
    else
      Data.decr { data with tape := tail }
  | [] => data -- unreachable code, return junk

def Data.right (data : Data) : Data :=
  let index := data.index + 1
  let tape := if index < data.tape.length then data.tape else 0 :: data.tape
  { tape, index }

def Data.left (data : Data) : Data :=
  { data with index := data.index - 1 }

def _root_.UInt8.toHex (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  "".pushn '0' (2 - s.length) ++ s

partial def Data.toString (data : Data) (tag := true): String :=
  match data.tape with
  | head :: tail =>
    let (current, tag) :=
      if tag = true ∧ data.index = data.tape.length - 1 then
        (s!"[{head.toHex}]", false)
      else
        (head.toHex, tag)
    let data : Data := { tape := tail, index := data.index - 1 }
    let remain := data.toString (tag := tag)
    remain ++ " " ++ current
  | [] => ""

def test_data : Data := ({} : Data).right.incr.right.incr.incr

#eval test_data.toString

end V1

/-!


Version 2 : IO
--------------------------------------------------------------------------------

Version 3 : Loops
--------------------------------------------------------------------------------

-/
