
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

Version 2 : IO
--------------------------------------------------------------------------------

Version 3 : Loops
--------------------------------------------------------------------------------

-/
