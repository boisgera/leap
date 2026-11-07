/-
TODO:

  - TODO: see how read works in practice. Put a prompt? Does it work in
    the playground?

  - baby brainfuck, simplified as much as possible?
    Boolfuck? HQ9+? 1L (https://esolangs.org/wiki/1L_a)?

  - brainfuck by steps: no IO first but return data at the end (?)
    no "[" and "]"" at first?

  - need testing

  - need parser (with characters others than listed ignored)

  - add a "dump" instruction?

  - improve read/write wrt to non-printable characters

  - Thoughts: the structure with IO for everything sucks. I don't mind eval
    being in IO but I don't like that for next. I'd rather add an optional
    IO Unit field to the state and handle it in the eval loop.

  - Then use the State monad somehow when that's cleaned up?

  - lift more methods to the Tape and Prg? Encapsulate indices in Tape and
    Prg?

  - Spoon binary encoding/decoding?

-/

namespace BrainFuck

abbrev Byte := UInt8

/-
An infinite read-write binary data tape initialized with zeroes
-/

def Tape := List Byte deriving ToString, Repr, Inhabited

def Tape.mk (bytes : List Byte) : Tape := bytes

def Tape.toList (tape : Tape): List Byte := tape

def Tape.get (tape : Tape) (i : Nat) : Byte :=
  if h : i <  tape.length then
    tape.toList[i]
  else
    0

def Tape.set (tape : Tape) (i : Nat) (byte : Byte) : Tape :=
  let tape := if i < tape.length then
    tape
  else
    tape.toList ++ (List.replicate (i - tape.length + 1) 0)
  tape.toList.set i byte

#eval Tape.mk []
-- []

#eval Tape.mk [1, 2, 3] |>.get 2
-- 3

#eval Tape.mk [1, 2, 3] |>.get 3
-- 0

#eval Tape.mk [1, 2, 3] |>.set 2 4
-- [1, 2, 4]

#eval Tape.mk [1, 2, 3] |>.set 6 4
-- [1, 2, 3, 0, 0, 0, 4]

inductive Instruction where
  | shiftRight
  | shiftLeft
  | increment
  | decrement
  | write
  | read
  | jumpForward
  | jumpBackward
--  | dump
--  | exit
deriving Repr, Inhabited, BEq

def Instruction.toString (i : Instruction) : String :=
  match i with
  | shiftRight => ">"
  | shiftLeft => "<"
  | increment => "+"
  | decrement => "-"
  | write => "."
  | read => ","
  | jumpForward => "["
  | jumpBackward => "]"

instance : ToString Instruction where
  toString := Instruction.toString

def Program := List Instruction deriving Repr, Inhabited, BEq

def Program.mk (instructions : List Instruction) : Program :=
  instructions

def Program.toList (prg : Program) : List Instruction :=
  prg

def Program.toString (prg : Program) : String :=
  "".intercalate (prg.map (fun instruction => s!"{instruction}"))

instance : ToString Program where
  toString := Program.toString

def printData : Program := [.jumpForward, .write, .shiftRight, .jumpBackward]

#eval IO.println s!"{printData}"
-- [.>]

partial def Program.parse (code : String) : Program :=
  match code.data with
  | [] => []
  | c :: cs => (match c with
      | '>' => .shiftRight
      | '<' => .shiftLeft
      | '+' => .increment
      | '-' => .decrement
      | '.' => .write
      | ',' => .read
      | '[' => .jumpForward
      | ']' => .jumpBackward
      | _ => panic! "invalid instruction" -- Be more forgiving here?
    ) :: (Program.parse (String.mk cs))

#eval Program.parse "[.>]"
-- [BrainFuck.Instruction.jumpForward,
--  BrainFuck.Instruction.write,
--  BrainFuck.Instruction.shiftRight,
--  BrainFuck.Instruction.jumpBackward]

def helloWorldSrc := "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."

def helloWorld := Program.parse helloWorldSrc

#eval s!"{helloWorld}" == helloWorldSrc
-- true

def Program.matchBracket! (prg : Program) (i : Nat) : Nat := Id.run do
  if prg.toList[i]! == .jumpForward then
    let mut c : Int := 1
    let mut j := i + 1
    while j < prg.length do
      if prg.toList[j]! == .jumpForward then
         c := c + 1
      else if prg.toList[j]! == .jumpBackward then
         c := c - 1
      if c == 0 then
        break
      j := j + 1
    if j < prg.length then
      return j
    else
      panic! "Unbalanced brackets"
  else if prg.toList[i]! == .jumpBackward then
    let mut c : Int := -1
    let mut j : Int := (Int.ofNat i) - 1
    while 0 <= j do
      if prg.toList[j.toNat]! == .jumpForward then
         c := c + 1
      else if prg.toList[j.toNat]! == .jumpBackward then
         c := c - 1
      if c == 0 then
        break
      j := j - 1
    if 0 <= j then
      return j.toNat
    else
      panic! "Unbalanced brackets"
  else
    panic! "indexed value is not a bracket"

#eval s!"{printData}"
-- "[.>]"

#eval printData.matchBracket! 0
-- 3

#eval printData.matchBracket! 3
-- 0

#eval s!"{helloWorld}"
-- "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."

#eval helloWorld.matchBracket! 8
-- 48

#eval helloWorld.matchBracket! 14
-- 33

#eval helloWorld.matchBracket! 33
-- 14

#eval helloWorld.matchBracket! 43
-- 45

#eval helloWorld.matchBracket! 45
-- 43

#eval helloWorld.matchBracket! 48
-- 8

/-

Execution state is the stuff in State:
  - Some program,
  - an instruction pointer (default value)
  - some data (default value),
  - some data pointer (default value)

and some (optional) side-effect, which is a state-altering IO action.

-/

structure State where
  prg : Program
  i : Nat := 0 -- instruction pointer
  data: Tape := []
  j : Nat := 0 -- data pointer
deriving Repr, Inhabited

instance : ToString State where
  toString := fun (state : State) =>
    s!"prg: {state.prg}\ni: {state.i}\ndata: {state.data}\nj: {state.j}"

abbrev SideEffect := Option (State -> IO State)

def next (state : State) : SideEffect × State :=
  match state.prg.toList[state.i]! with
  | .shiftRight => (none, { state with i := state.i + 1, j := state.j + 1 })
  | .shiftLeft  => (none, { state with i := state.i + 1, j := state.j - 1 })
  | .increment  => (none, { state with i := state.i + 1, data := state.data.get state.j |> (· + 1) |> state.data.set state.j })
  | .decrement  => (none, { state with i := state.i + 1, data := state.data.get state.j |> (· - 1) |> state.data.set state.j })
  | .write => -- ⚠️ only works for printable ASCII chars
    let action := fun (state : State) => do
      IO.println s!"output: {(Char.ofNat (state.data.get state.j).toNat)}"
      -- IO.print (Char.ofNat (state.data.get state.j).toNat)
      return state
    (some action, { state with i := state.i + 1})
  | .read => -- ⚠️ only works for printable ASCII chars
    let action := fun (state : State) => do
      IO.print "input: "
      let stdin <- IO.getStdin
      let line <- stdin.getLine
      let char := line.front
      let number := char.toUInt8
      return { state with data := state.data |>.set state.j number}
    (some action, { state with i := state.i + 1 })
  | .jumpForward => -- 🪲 need to find the *matching* ]
    if (state.data.get state.j) == 0 then
      let i' := (state.prg.drop (state.i + 1)).findIdx (· matches .jumpBackward)
      (none, { state with i := (state.i + 1) + i' + 1 })
    else
      (none, { state with i := (state.i + 1) })
  | .jumpBackward => -- 🪲 need to find the *matching* [
    let i := state.prg.take state.i |>.findIdx (· matches .jumpForward)
    (none, { state with i := i})

-- Warning: will panic if the instruction pointer is out-of-bounds
def evalNext (state : State) : IO State := do
  let (effect, state) := next state
  -- dbg_trace s!"*** {state}"
  if let some action := effect then
    action state
  else
    return state

/- TODO: return data instead of returning nothing? -/
partial def eval (state : State) : IO Unit := do
  let mut state := state
  -- dbg_trace s!"{state}"
  while state.i < state.prg.length do
    state <- evalNext state

def hello : State :=
  {
    prg := [.jumpForward, .write, .shiftRight, .jumpBackward] -- "[.>]"
    i := 0
    data := "Hello world!".data.map (fun c => UInt8.ofNat c.toNat)
    j := 0
  }

#eval eval hello

def readWriteLoop := Program.parse "+[>,.<]"

-- #eval eval { prg := readWriteLoop : State }


end BrainFuck

def main := BrainFuck.eval { prg := BrainFuck.readWriteLoop }
