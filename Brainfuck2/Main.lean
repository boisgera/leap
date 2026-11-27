namespace Brainfuck

namespace V1


structure Data where
  tape : List UInt8 := [0] -- reversed
  index : Nat := 0         -- *not* reversed (convenient to have index ≥ 0)

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
  commands : List Command := []

def Program.toString (program : Program) : String :=
  program.commands
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
  return (prg.exec {}) |>.2 |>.toString
  : Option String
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
  return data.toString
  : Option String
)

/-!
We can also use an inner do block with the state monad to have a more convenient
combination of program executions.
-/

#eval (do
  let prg1 ← parse ">+>++"
  let prg2 ← parse "<+<++"
  let combinedExec : DataM Unit := do prg1.exec ; prg2.exec
  return combinedExec.run {} |>.2 |>.toString
  : Option String
)

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
      IO.println data.toString
  return 0


end V1

namespace V2

mutual

inductive Command where
  | incr
  | decr
  | left
  | right
  | read
  | write
  | loop (program : Program)

structure Program where
  commands : List Command := []

end

mutual

partial def Command.toString (command : Command) : String :=
  match command with
  | .incr => "+"
  | .decr => "-"
  | .left => "<"
  | .right => ">"
  | .read => ","
  | .write => "."
  | .loop program => s!"[{program.toString}]"

partial def Program.toString (program : Program) : String :=
  program.commands
    |>.map Command.toString
    |> "".intercalate

end

structure Data where
  tape : List UInt8 := [0] -- reversed
  index : Nat := 0         -- *not* reversed (convenient to have index ≥ 0)

partial def Data.set (byte : UInt8) (data : Data) : Data :=
  match data.tape with
  | head :: tail =>
    if data.index = data.tape.length - 1 then
      { data with tape := byte :: tail }
    else
      let newData := Data.set byte { data with tape := tail }
      { newData with tape := head :: newData.tape }
  | [] => data -- unreachable code, return junk

partial def Data.get (data : Data) : UInt8 :=
  match data.tape with
  | head :: tail =>
    if data.index = data.tape.length - 1 then
      head
    else
      Data.get { data with tape := tail }
  | [] => 0 -- unreachable code, return junk

partial def Data.read (data : Data) : IO Data := do
  let stdin ← IO.getStdin
  let bytes ← stdin.read 1
  let byte := bytes[0]!
  return data.set byte

partial def Data.write (data : Data) : IO Unit := do
  let byte := data.get
  let byteArray := ByteArray.mk #[byte]
  let stdout ← IO.getStdout
  stdout.write byteArray
  stdout.flush

partial def Data.incr (data : Data) : Data :=
  data.get |> (· + 1) |> data.set

partial def Data.decr (data : Data) : Data :=
  data.get |> (· - 1) |> data.set

def Data.right (data : Data) : Data :=
  let index := data.index + 1
  let tape := if index < data.tape.length then data.tape else 0 :: data.tape
  { tape, index }

def Data.left (data : Data) : Data :=
  { data with index := data.index - 1 }

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

def testData : Data := ({} : Data).right.incr.right.incr.incr

#guard testData.toString = "00 01 [02]"
#guard testData.right.toString = "00 01 02 [00]"
#guard testData.left.toString = "00 [01] 02"
#guard testData.incr.toString = "00 01 [03]"
#guard testData.decr.toString = "00 01 [01]"

abbrev DataM := StateT Data IO

def read : DataM Unit := fun data => do
  let data ← data.read ; return ((), data)
def write : DataM Unit := fun data => do
  data.write ; return ((), data)
def incr : DataM Unit := modify Data.incr
def decr : DataM Unit := modify Data.decr
def left: DataM Unit := modify Data.left
def right : DataM Unit := modify Data.right

mutual

partial def Command.exec (command : Command) : DataM Unit := do
  match command with
  | .incr => V2.incr
  | .decr => V2.decr
  | .left => V2.left
  | .right => V2.right
  | .read => V2.read
  | .write => V2.write
  | .loop program => do
      let data ← get
      if data.get ≠ 0 then
        let prg : Program := {
          commands := program.commands ++ [Command.loop program]
        }
        prg.exec

partial def Program.exec (program : Program) : DataM Unit := do
  match program.commands with
  | [] => return
  | command :: commands =>
    -- dbg_trace (s!"command: {command.toString}")
    command.exec
    { commands : Program }.exec

end

/--
Read one symbol, display the symbol and the next two in ASCII order
-/
def test : IO Unit := do
  let program : Program := {
    commands := [
      .read,
      .right,
      .incr,
      .incr,
      .incr,
      .loop { commands := [.left, .write, .incr, .right, .decr] }
    ]
  }
  IO.println s!"program: {program.toString}"
  _ ← program.exec.run {}

abbrev ParserM := StateT (List Char) Option

def parseIncr : ParserM Command := do
  match (← get) with
  | '+' :: tokens =>
    set tokens
    return Command.incr
  | _ => failure

def parseDecr : ParserM Command := do
  match (← get) with
  | '-' :: tokens =>
    set tokens
    return Command.decr
  | _ => failure

def parseLeft : ParserM Command := do
  match (← get) with
  | '<' :: tokens =>
    set tokens
    return Command.left
  | _ => failure

def parseRight : ParserM Command := do
  match (← get) with
  | '>' :: tokens =>
    set tokens
    return Command.right
  | _ => failure

def parseRead : ParserM Command := do
  match (← get) with
  | ',' :: tokens =>
    set tokens
    return Command.read
  | _ => failure

def parseWrite : ParserM Command := do
  match (← get) with
  | '.' :: tokens =>
    set tokens
    return Command.write
  | _ => failure

def parseSimpleCommand : ParserM Command :=
  parseIncr
  <|> parseDecr
  <|> parseLeft
  <|> parseRight
  <|> parseRead
  <|> parseWrite

def parseOpenBracket : ParserM Unit := do
  match (← get) with
  | '[' :: tokens =>
    set tokens
  | _ => failure

def parseClosedBracket : ParserM Unit := do
  match (← get) with
  | ']' :: tokens =>
    set tokens
  | _ => failure

mutual

partial def parseCommand : ParserM Command :=
  parseSimpleCommand <|> parseLoop

partial def parseLoop : ParserM Command := do
  parseOpenBracket
  let commands ← parseCommands
  parseClosedBracket
  return Command.loop { commands := commands }

partial def parseCommands : ParserM (List Command) := do
  let mut commands := []
  repeat
    try
      commands := (← parseCommand) :: commands
    catch _ =>
      break
  return commands.reverse

end

def parse (src : String) : Option Program :=
  let tokens := src.toList
  match parseCommands.run tokens with
  | some (commands, []) => return { commands } -- parsed up to the end
  | _ => failure -- error (impossible actually) or partial parse

#eval do
  let prg ← parse ",>+++[<.+>-]"
  return prg.toString

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  match args with
  | [] => stderr.putStrLn "brainfuck2 [FILE.bf]" ; return 1
  | filename :: _ =>
    let src ← IO.FS.readFile filename
    let prg? := parse src
    match prg? with
    | none =>
      stderr.putStrLn "invalid program" ; return 1
    | some prg =>
      _ ←  prg.exec {} -- discard data
  return 0
end V2

end Brainfuck

-- def main := Brainfuck.V1.main
def main := Brainfuck.V2.main
