/-
TODO:

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
deriving Repr, Inhabited

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

def Program := List Instruction deriving Repr, Inhabited

def Program.toList (prg : Program) : List Instruction :=
  prg

def Program.toString (prg : Program) : String :=
  "".intercalate (prg.map (fun instruction => s!"{instruction}"))

instance : ToString Program where
  toString := Program.toString

/-
Execution state is: Some program, an instruction pointer (optional) some data (optional), some data pointer (optional)
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
  | .write => -- TODO: improve when not printable? (e.g. use \x??)
    let action := fun (state : State) => do
      IO.println s!"output: {(Char.ofNat (state.data.get state.j).toNat)}"
      -- IO.print (Char.ofNat (state.data.get state.j).toNat)
      return state
    (some action, { state with i := state.i + 1})
  | .read => -- TODO: improve to deal with non-printable chars.
    let action := fun (state : State) => do
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


end BrainFuck
