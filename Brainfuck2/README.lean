
/-!

Preamble
--------------------------------------------------------------------------------

  - [ ] Learn the basics about [Brainfuck], its syntax, data and execution.

  - [ ] Create a top-level `Brainfuck` namespace and child namespaces
    `V1` and `V2` version namespaces.

[Brainfuck]: https://en.wikipedia.org/wiki/Brainfuck


Data
--------------------------------------------------------------------------------

In this section, everything takes place in `V1`.

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

  - [ ] With `DataM` an alias for `StateM Data`, implement variants of the
    `incr`, `decr`, `left` and `right` in the root namespace
    with type `DataM Unit` using your previous implementations.


### Program execution

  - [ ] Define a new `Command` type with constructors `incr`, `decr`,
    `left` and `right` (with no arguments) and its `toString` method
    that return the original symbol as a `String`.

  - [ ] Define a `Command.exec` method of type `Command → DataM Unit`
    that executes a single command.

  - [ ] Define `Program` as a structure that contains a list of commands,
    and the associated `toString` method that is a valid source representation
    of the Brainfuck program.

  - [ ] Implement the `Program.exec` method which executes a program.

### Parser

  - [ ] Define a `parse` function that turns a `String` supposed to represent
    the content of a valid Brainfuck program into an `Option Program`
    (use `none` when the source is actually invalid). Use a monadic style
    when appropriate!

### Command-line interface

  - [ ] Define a `main` function that reads the filename of a Brainfuck program
    with only the `+`, `-`, `<` and `>` symbols, parses it, executes it and
    displays the tape at the end of the execution.


IO & Loops
--------------------------------------------------------------------------------

In this section, everything takes place in `V2`.

### Program

 - [ ] Create a new version of the `Command` type with three new constructors:
   `read`, `write` and a `loop` constructor that takes a `Program` as an
   argument. Replicate your definition of `Program` in the `V2` namespace,
   as well as the `toString` methods.

### Data

  - [ ] Introduce a new version of the `Data` type which has `read` and `write`
    methods which read from the standard input to set the current tape byte
    and write the current tape to the standard output respectively.
    What are their signature? "Copy" the `incr`, `decr`, `left` and `right`
    methods from `V1`. Then, adapt the the definition of `DataM` in order to
    get a consistent set of monadic actions `read`, `write`, `incr`, `decr`,
    `left` and `right` in `V2` of value `DataM α` with a suitable `α`.

### Program execution

  - [ ] Define a `Command.exec` method of type `Command → DataM Unit`
    that executes a single command and `Program.exec` method which
    executes a complete program.

### Parser

With the introduction of loops, that is brackets at the source level,
our parser gets more complicated. We will build it out of smaller,
specialized small parser that consume part of the program source, or fail.

The signature each of these parser is `List Char → Option (α × (List Char))`
for some type `α`, or equivalently if we define `ParserM` as
`StateT (List Char) Option`, their type is `ParserM α`.

 - [ ] Implement `parseIncr`, `parseDecr`, `parseLeft` and `parseRight`
  that read a single token from the programme source (or fail if it's
  impossible) and return the appropriate `Command` if the token is
  `+`, `-`, `<`, `>`, `,` or `,` and fails otherwise.

- [ ] Combine the four parsers above into a single `parseSimpleCommand`
  parser that returns a command.

 - [ ] Implement `parseOpenBracket` and `parseCloseBracket` that read the tokens
  `[` and `]` respectively or fail if it's not possible.

 - [ ] Then using mutual definitions, implement

     - [ ] `parseCommand` which parses either a simple command or a loop,

     - [ ] `parseCommands` which parses any number (including zero) of commands
       and returns a list (this parser always succeed). Make sure that its
       implementation is *greedy*: it should parses the largest sequence of
       commands and return only when it reaches the end of the source or
       invalid commands.

     - [ ] `parseLoop` that succeeds if it can parse an open bracket,
       then any number of command

 - [ ] Create a `parse` function that consumes a program source (a string)
  and returns and `Option Program` (parsing that does not go to the end
  of the source should be treated as a failure).

### Command-line interface

  - [ ] Define a `main` function that reads the filename of a Brainfuck program,
    parses it and executes it.


Appendix/notes
--------------------------------------------------------------------------------

A structure based on a (reversed) list + index "works" for the `Data` but:

  - the implementation of `incr` and `decr` below don't *feel* right,
    later with `read` and `write` you realize that you actually need
    more general `get` and `set` methods to do the work.

  - their execution performance depends linearly on the length of the list.

Two alternate solutions:

  - an `Array`-based solution (random access is cheap),

  - a `Zipper`-based solution, where

    ```lean4
    structure Zipper (α : Type) where
      left  : List α -- reversed prefix
      current : α
      right : List α
    ```

    which makes elementary operations work in constant time and have trivial
    `get` and `set` methods.


-/
