
namespace Brainfuck

abbrev Byte := UInt8

inductive Instruction where
  | left  -- <
  | right -- >
  | decr  -- -
  | incr  -- +
  | read  -- ,
  | write -- .
  | loop (instructions : List Instruction) -- [ ]
  deriving Repr -- TODO: provide a shorter repr, with the symbols.

abbrev Parser := StateT (List Char) Option

def parseSymbol : Parser Instruction := do
  match (<- get) with
  | [] => failure
  | '<' :: cs => set cs ; return .left
  | '>' :: cs => set cs ; return .right
  | '-' :: cs => set cs ; return .decr
  | '+' :: cs => set cs ; return .incr
  | ',' :: cs => set cs ; return .write
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

-- TODO: I probably need to default here to a parser that consumes
-- as much as it can for me to be able to recurse properly.
-- So I can't just branch to a "[" match when I locally fail...
-- Here parse is actually "parseGreedyBalanced"...
partial def parse : Parser (List Instruction) := do
  let mut instructions : List Instruction := []
  if (<- get) != [] then
    try
      instructions := instructions.concat (<- parseSymbol)
      instructions := instructions.append (<- parse)
    catch _ =>
      dbg_trace s!"*** {repr (<- get)}"
      parseOpeningLoop
      -- nah, after this point, the parse will choke on ']'.
      -- The current code is buggy. Use another argument which
      -- is a counter of open '[' ?
      -- Draw a graph first to see the pattern.
      -- This is probably simpler.
      -- do I need a "parse until you can't, don't fail and forget"
      -- version of parse?
      instructions := instructions.concat (Instruction.loop (<- parse))
      parseClosingLoop
      -- second case: it's a closing loop. What do we do? we just fail
      -- and see if the caller can handle it?
  return instructions

#eval parse.run []
-- some ([], [])

#eval parse.run ['+']
-- some ([Brainfuck.Instruction.incr], [])

#eval parse.run ['+', '-']
-- some ([Brainfuck.Instruction.incr, Brainfuck.Instruction.decr], [])

#eval parse.run ['[', ']']

/-!
TODO: Zipper-like structure to represent the tape.
Auto-grows (if needed) when we move right (better than the original 30,000 cells!)
-/

/-!
>	move the data pointer right
<	move the data pointer left
+	increment the byte at the pointer
-	decrement the byte at the pointer
.	output the byte at the pointer (as an ASCII character)
,	read one byte of input into the cell at the pointer
[	if the current cell is 0, jump forward to the matching ]
]	if the current cell is nonzero, jump back to the matching [
-/

end Brainfuck
