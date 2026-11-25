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
    0, 255, 127 and 255 and with a pointer to the third cell like
    `00 ff [7f] ff`.

    Then declare an instance of `ToString Data` with:
    ```
    instance : ToString Data where
      toString := Data.toString
    ```

  - [ ] With `DataM` an alias for `StateM Data`, implement variants of the
    `incr`, `decr`, `left` and `right` in the root namespace
    with type `DataM Unit` using your previous implementations.


### Program execution

  - [ ] Define a new `Command` type with constructors `incr`, `decr`,
    `left` and `right` (with no arguments) and its `toString` method
    that return the original symbol as a `String`.
    Define the corresponding instance of `ToString Command`.

  - [ ] Define a `Command.exec` method of type `Command → DataM Unit`
    that executes a single command.

  - [ ] Define `Program` as a structure that contains a list of commands,
    and the associated `toString` method that is a valid source representation
    of the Brainfuck program. Define the corresponding instance of
    `ToString Program`.

  - [ ] Implement the `Program.exec` method which executes a program.

### Parser

  - [ ] Define a `parse` function that turns a `String` supposed to represent
    the content of a valid Brainfuck program into an `Option Program`
    (use `none` when the source is actually invalid). Use a monadic style
    when appropriate!

### Command-line interface

  - [ ] Define a `main` function that reads the filename of a Brainfuck program,
    parses it, executes it and display the tape at the end of the execution.

-/

namespace Brainfuck

namespace V1

structure Data where
  tape : List UInt8 := [0] -- reversed
  index : Nat := 0         -- *not* reversed (convenient to have index ≥ 0)

/-!
OF COURSE NOT! That's truncating the tape!
-/
partial def Data.incr (data : Data) : Data :=
  match data.tape with
  | head :: tail =>
    if data.index = data.tape.length - 1 then
      { data with tape := (head + 1) :: tail }
    else
      let incrData := Data.incr { data with tape := tail }
      { incrData with tape := head :: incrData.tape }
  | [] => data -- unreachable code, return junk

partial def Data.decr (data : Data) : Data :=
  match data.tape with
  | head :: tail =>
    if data.index = data.tape.length - 1 then
      { data with tape := (head - 1) :: tail }
    else
      let decrData := Data.decr { data with tape := tail }
      { decrData with tape := head :: decrData.tape }
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

partial def Data.toStringAux (data : Data) (tag : Bool) : List String :=
  match data.tape with
  | head :: tail =>
    let (current, tag) :=
      if tag = true ∧ data.index = data.tape.length - 1 then
        (s!"[{head.toHex}]", false)
      else
        (head.toHex, tag)
    let data : Data := { tape := tail, index := data.index }
    let remain := data.toStringAux tag
    current :: remain
  | [] => []

def Data.toString (data : Data) : String :=
  data.toStringAux (tag := true)
    |>.reverse
    |> " ".intercalate

instance : ToString Data where
  toString := Data.toString

def testData : Data := ({} : Data).right.incr.right.incr.incr

#guard testData.toString = "00 01 [02]"
#guard testData.right.toString = "00 01 02 [00]"
#guard testData.left.toString = "00 [01] 02"
#guard testData.incr.toString = "00 01 [03]"
#guard testData.decr.toString = "00 01 [01]"

abbrev DataM := StateM Data

def incr : DataM Unit := modify Data.incr
def decr : DataM Unit := modify Data.decr
def left: DataM Unit := modify Data.left
def right : DataM Unit := modify Data.right

def modifyTestData : DataM Unit := do
  left ; incr
  left ; incr ; incr

def testData2 :=
  testData          -- start with testData
  |> modifyTestData -- i.e. apply modifyTestData.run
  |>.2              -- get the state out of the (value, state) pair

#guard testData2.toString == "[02] 02 02"

inductive Command where
  | incr
  | decr
  | left
  | right

def Command.toString (command : Command) : String :=
  match command with
  | incr => "+"
  | decr => "-"
  | left => "<"
  | right => ">"

def Command.exec (command : Command) : DataM Unit :=
  match command with
  | incr => V1.incr
  | decr => V1.decr
  | left => V1.left
  | right => V1.right

structure Program where
  commands : List Command := [] -- reversed

def Program.toString (program : Program) : String :=
  program.commands
    |>.reverse
    |>.map Command.toString
    |> "".intercalate

partial def Program.exec (program : Program) : DataM Unit := do
  match program.commands with
  | [] => return
  | command :: commands =>
    command.exec
    { commands : Program }.exec

def parseSymbol (symbol : Char) : Option Command :=
  match symbol with
  | '+' => Command.incr
  | '-' => Command.decr
  | '<' => Command.left
  | '>' => Command.right
  | _   => failure

partial def parseAux (symbols : List Char) : Option Program := do
  match symbols with
  | symbol :: symbols =>
    let command ← parseSymbol symbol
    let commands := (← parseAux symbols).commands
    let commands := command :: commands
    return { commands }
  | [] => some {}

def parse (src : String) : Option Program :=
  parseAux src.toList

/-!
This is how we would parse & run a program and display the tape
-/
#eval (do
  let prg ← parse ">+>++"
  return (prg.exec {}) |>.2
  : Option Data
)

/-!
`Program.exec` is a tape mutator ; we can chain the exec of two programs
-/
#eval (do
  let prg1 ← parse ">+>++"
  let prg2 ← parse "<+<++"
  let mut data : Data := {}
  (_, data) := prg1.exec data
  (_, data) := prg2.exec data
  return data
  : Option Data
)

/-!
We can also use an inner do block with the state monad to have a more convenient
combination of program executions.
-/

#eval (do
  let prg1 ← parse ">+>++"
  let prg2 ← parse "<+<++"
  let combinedExec : DataM Unit := do prg1.exec ; prg2.exec
  return combinedExec.run {} |>.2
  : Option Data
)

end V1

end Brainfuck

open Brainfuck.V1 in
def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  match args with
  | [] => stderr.putStrLn "brainfuck2 [FILE.bf]" ; return 1
  | filename :: _ =>
    let src ← IO.FS.readFile filename
    let prg? := parse src
    match prg? with
    | none => stderr.putStrLn "invalid program" ; return 1
    | some prg =>
      let data := (prg.exec {}).2
      IO.println data
  return 0
