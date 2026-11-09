namespace Brainfuck

abbrev Byte := UInt8

inductive Command where
  | left  -- <
  | right -- >
  | decr  -- -
  | incr  -- +
  | read  -- ,
  | write -- .
  | loop (code : List Command) -- [...]

def Command.toString (cmd : Command) : String :=
  match cmd with
  | left => "<"
  | right => ">"
  | decr => "-"
  | incr => "+"
  | read => ","
  | write => "."
  | loop code => s!"[{code.map toString |> "".intercalate}]"

instance : ToString Command where
  toString := Command.toString

instance : ToString (List Command) where
  toString (commands) := commands.map toString |> "".intercalate

/-!
Instead of an array of 30,000 bytes, we grow the array dynamically.
We also use a Zipper design to have each elementary operation
made in constant time.

Step:
- consider only the pure actions to begin with (not read/write).
- implement a simple tape architecture first (array ?), then the zipper
- update to take into account read/write with IO Tape return type
- adopt the appropriate StateT structure.
- play with get and set, see how modify can help.

-/
structure Tape where
  beforeReversed : List Byte := []
  current : Byte := 0
  after : List Byte := []

abbrev Tape.Action := StateT Tape IO Unit
-- aka Tape -> IO (Unit × Tape) which is a bit dumb...
-- go for Tape -> Tape × IO Unit instead?
-- Mmmm there is at least one case where we need Tape inside the IO
-- So that would be Tape -> IO Tape

def Tape.left : Action := do
  modify fun tape =>
    match tape.beforeReversed with
    | [] => tape
    | head :: tail => {
        beforeReversed := tail,
        current := head,
        after := tape.current :: tape.after
      }

def Tape.right : Action := do
  modify fun tape =>
    match tape.after with
    | [] => {
        beforeReversed := tape.current :: tape.beforeReversed,
        current := 0,
        after := [],
        : Tape
      }
    | head :: tail => {
        beforeReversed := tape.current :: tape.beforeReversed,
        current := head,
        after := tail,
        : Tape
      }

def Tape.decr : Action :=
  modify fun tape => { tape with current := tape.current - 1 }

def Tape.incr : Action :=
  modify fun tape => { tape with current := tape.current + 1 }

def Tape.read : Action := do
  let tape <- get
  let stdin <- IO.getStdin
  let bytes <- stdin.read 1
  -- we interpret EOF as 0
  let byte : UInt8 := if bytes.isEmpty then 0 else bytes[0]!
  set { tape with current := byte }

def Tape.write : Action := do
  let tape <- get
  let stdout <- IO.getStdout
  stdout.write (ByteArray.mk #[tape.current])

partial def Tape.exec (code : List Command) : Action := do
  match code with
  | [] => return
  | inst :: code =>
    match inst with
    | .left => Tape.left ; Tape.exec code
    | .right => Tape.right ; Tape.exec code
    | .decr => Tape.decr ; Tape.exec code
    | .incr => Tape.incr ; Tape.exec code
    | .read => Tape.read ; Tape.exec code
    | .write => Tape.write ; Tape.exec code
    | .loop inner =>
      let tape <- get
      if tape.current ≠ 0 then
        Tape.exec inner
        Tape.exec (inst :: code)
      else
        Tape.exec code

/-!
A step-by-step evaluator that we could rebuild exec on.
Useful for pedagogical issues and debugging!
Also, since this is not recursive or partial, we can do proofs with it!
-/

abbrev Stack := List (List Command)

/-!
TODO: cleaner (Stream?) api for termintation. Mmm Stream doesn't perfectly
      fit, it's not monadic. Arf, shoot... Anyway we need at least a better
      termination? Or just test manually with a helper function?
      Well, actually we could do some `Stream (Stack × Tape) (IO Unit)`,
      the use API would be very simple AFAICT.
      The associated `next?` function would (def eq to)
      `StateT (Stack × Tape) Option (IO Unit)`.
      `none` represents the end of the iteration (at this stage we
      have 0 other kind of errors).
      But then is there a mismatch with the Action API above?
      Think of it, I felt that the Action modelling was klunky anyway.

      Update: that doesn't WORK. read needs to IO context to generate the
      new tape. Do we need to pick `IO (Stack × Tape)` as the stream
      type?


TODO: cleaner, more imperative version.
TODO: turn this (Stack × Tape) -> IO (Unit × (Stack × Tape)) into
a (Stack × Tape) -> Option (IO (Unit × (Stack × Tape)))?

To begin with, just make a helper function that reads if Stack is empty
(to test the end of the code execution)? I don't know. The
  match stack with
  | [] => return
feels like it want to return a none.

OK keep this one like that and add a next? version on top of it,
with signature (Stack × Tape) -> OptionT IO (Stack × Tape)
(which means IO (Option (Stack × Tape)))

TODO: def Machine := Stack × Tape ?
-/
def Tape.next : StateT (Stack × Tape) IO Unit  := do
  let (stack, tape) <- get
  match stack with
  | [] => return
  | code :: stack =>
    match code with
    | [] =>
      set (stack, tape)
    | inst :: code =>
      match inst with
      | .left =>
        let (_, tape) <- tape.left -- equiv to "Tape.read then 'advance'?"
        set (code :: stack, tape)
      | .right =>
        let (_, tape) <- tape.right
        set (code :: stack, tape)
      | .decr =>
        let (_, tape) <- tape.decr
        set (code :: stack, tape)
      | .incr =>
        let (_, tape) <- tape.incr
        set (code :: stack, tape)
      | .read =>
        let (_, tape) <- tape.read
        set (code :: stack, tape)
      | .write =>
        let (_, tape) <- tape.write
        set (code :: stack, tape)
      | .loop inner =>
        if tape.current ≠ 0 then
          set (inner :: (inst :: code) :: stack, tape)
        else
          set (code :: stack, tape)




/-!
--------------------------------------------------------------------------------
-/

abbrev Parser := StateT (List Char) Option

def parseSymbol : Parser Command := do
  match (<- get) with
  | [] => failure
  | '<' :: cs => set cs ; return .left
  | '>' :: cs => set cs ; return .right
  | '-' :: cs => set cs ; return .decr
  | '+' :: cs => set cs ; return .incr
  | ',' :: cs => set cs ; return .read
  | '.' :: cs => set cs ; return .write
  | _ => failure

def parseOpeningLoop : Parser Unit := do
  match (<- get) with
  | '[' :: cs => set cs
  | _ => failure

def parseClosingLoop : Parser Unit := do
  match (<- get) with
  | ']' :: cs => set cs
  | _ => failure

-- Mmm think of an architecture where it's easy to prove termination.
-- Easy enough as it is? (Grmph ...)

partial def parseZeroOrMore {α} (p : Parser α) : Parser (List α) := do
  try
    let a <- p
    let as <- parseZeroOrMore p
    return a :: as
  catch _ =>
    return []

mutual

partial def parseCommands := parseZeroOrMore parseCommand

partial def parseCommand : Parser Command := do
  try
    parseSymbol
  catch _ =>
    parseOpeningLoop
    let cmds <- parseCommands
    parseClosingLoop
    return Command.loop cmds

end

def parse (source : String) : Except String (List Command) :=
  let chars := source.toList
  match parseCommands.run chars with
  | none => unreachable! -- zeroOrMore can't fail.
  | some (commands, []) => .ok commands
  | some (_, remain) => .error s!"parse failed at {String.ofList remain}"


#eval parse ""
-- ok:

#eval parse "+"
-- ok: +

#eval parse "++"
-- ok: ++

#eval parse "+-"
-- ok: +-

#eval parse "[]"
-- ok: []

#eval parse "[+-]"
-- ok: [+-]

#eval parse "@"
-- error: parse failed at @

#eval parse "+-[+-"
-- error: parse failed at [+-

end Brainfuck

/-!
TODO: write example codes, make a main function that executes the brainfuck file
(.bf or .🤯 extension).
-/

def usage : IO Unit :=
  IO.println "Usage: brainfuck [FILE.bf]"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => usage ; return 1
  | filename :: _ =>
    let source <- IO.FS.readFile filename
    let result := Brainfuck.parse source
    match result with
    | Except.error message =>
      IO.eprintln message
      return 1
    | Except.ok code =>
      let tape : Brainfuck.Tape := {}
      let _ <-  tape.exec code
      return 0
