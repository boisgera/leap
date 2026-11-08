A Brainfuck Interpreter
================================================================================

**TODO.**
- summarize Brainfuck the language, the concepts of tape, the interpretation of each command, etc.
- add references to wikipedia for details, to <https://brainfuck.org/> for code samples. 
- refer/explanation of the 3 local brainfuck examples.

The Abstract Syntax Tree
--------------------------------------------------------------------------------

**TODO.**
- Give the `Command` type
- ask for instances of `ToString Command` and `ToString List Command` that
  reproduce the Brainfuck code

The Tape
--------------------------------------------------------------------------------

**TODO.**
- Explain that the `Tape` type represent the data in the tape AND the 
  location of the current tape cell and that the tape is initially 
  filled with zeros.
- Give the pure subset of the `Tape` interface, ask for the classic design
  (array of 30,000 cells).
- Ask that we now search for a new implementation of `Tape` that 
  1. grows dynamically (starts "empty"), we add zeros in real time when
  we move left
  2. every basic tape action can be done in constant time (forget about a
  naive List implementation!). 
  Give a reference to the classic Zipper to help
- Add the read and write methods to Tape, change the previous ones so
  that they now produce a value in `IO Tape`.
- Introduce `abbrev Tape.Action := StateT Tape IO Unit`, rework the interface
  of all methods; use the get, set and/or modify associated API when it makes
  sense to streamline the implementations!

The Interpreter
--------------------------------------------------------------------------------

**TODO.** Please Claude, give some help to explain what 
`def Tape.exec (code : List Command) : Action`
should do and give some advice to break the job into simpler pieces.

The Parser
--------------------------------------------------------------------------------

**TODO.** Please Claude, explain the goald and decompose it into small 
steps and if needed layers of small refactoring as it was done in the 
section above.

The CLI
--------------------------------------------------------------------------------

TODO: Claude, tell what we expect, how to do it (steps) and how to test at least the 
three examples that are provided.
