import Std
open Std (HashMap)

/-!
TODO: easy CLI where short and long option needs to be a single token
=> there is no need to distinguish flags, optional and required.
-/

namespace EasyCLI

inductive Option where
  | short (c : Char)
  | long (s : String)

instance : ToString Option where
  toString (n : Option) :=
    match n with
    | .short c => s!"-{c}"
    | .long s => s!"--{s}" -- Q: render with = at the end?

instance : Repr Option where
  reprPrec option _ := repr (toString option)

#guard (Option.short 'h' |> toString) = "-h"
#guard (Option.long "help" |> toString) = "--help"

instance : BEq Option where
  beq (opt1 opt2 : Option) := toString opt1 == toString opt2

instance : Hashable Option where
  hash (option : Option) := hash (toString option)

abbrev OptionMap := HashMap Option (List String) -- Sh*it, this is unordered

instance : ToString OptionMap where
  toString (optionMap : OptionMap) := toString (repr optionMap.toList)

structure Result where
  options : OptionMap := {}
  args : List String := []

def Result.toString (result : Result) : String :=
  s!"options: {result.options} \n\
  args: {repr result.args}"

instance : ToString Result where
  toString := Result.toString

def Option.find? (options : List Option) (arg : String) : _root_.Option Option :=
  match options with
  | [] => none
  | option :: options =>
    if arg.startsWith s!"{option}" then
      option
    else
      Option.find? options arg

def parse (options : List Option) (args : List String) (result : Result := {}) : Result :=
  match args with
  | [] => result
  | arg :: args =>
    match Option.find? options arg with
    | none => -- unconventional choice here, reconsider?
      -- instead, detect ("--" or) anything that doesn't start with "-"
      -- and push all that remains as args?
      parse options args { result with args := result.args.concat arg }
    | some option =>
      let value := match option with
      | .short _ => arg.drop 2
      | .long s =>
        let eq_value := arg.drop (s.length + 2)
        if !eq_value.startsWith "=" then
          panic! "Use = to assign a value to a long option"
        else
          eq_value.drop 1
      let values := result.options.getD option [] |>.concat value.toString
      parse options args { result with options := result.options.insert option values }

/-!
TODO: panic on some option-like code with unregistered options.
-/

def options : List Option := [
  Option.short 'v',
  Option.long "help",
  Option.long "meme"
]

#eval parse options [
  "-v3", "-v++",
  "--help=",
  "--meme=Yup", "--meme=Yop",
  "Hello", "world!"
]
-- options: [("--help", [""]), ("--meme", ["Yup", "Yop"]), ("-v", ["3", "++"])]
-- args: ["Hello", "world!"]


end EasyCLI

/-!
--------------------------------------------------------------------------------
-/

namespace CLI

namespace Option

inductive Kind where
  | none     -- flag (false or true)
  | optional -- requires no space for short name and = for long ones
  | required

inductive Name where
  | short (c : Char)
  | long (s : String)

instance : ToString Name where
  toString (n : Name) :=
    match n with
    | Name.short c => s!"-{c}"
    | Name.long s => s!"--{s}"

#guard (Name.short 'h' |> toString) = "-h"
#guard (Name.long "help" |> toString) = "--help"

end Option

structure Option where
  name : Option.Name
  kind : Option.Kind

abbrev Map := HashMap String

structure Results where
  options : Map (List String) := {}
  args : List String := []

def Option.find? (options : List Option) (arg : String) : _root_.Option Option :=
  match options with
  | [] => none
  | option :: options =>
    if arg.startsWith s!"{option.name}" then
      option
    else
      Option.find? options arg

def parser (options : List Option) (args : List String) (results : Results := {}) : Results :=
  match args with
  | [] => results
  | arg :: args =>
    -- find the first option that fits arg, see what to do from here.
    sorry


end CLI

/-!

namespace DCLI -- CLI with dependently typed interface

class Parseable (α : Type) where
  parse? : String → Option α

instance : Parseable String where
  parse? := fun s => some s

instance : Parseable Nat where
  parse? := String.toNat?

instance : Parseable Bool where
  parse? := fun s =>
    match s with
    | "false" => some false
    | "true" => some true
    | _ => none

inductive Option.Kind where
  | none -- flag -> false or true
  | optional (α : Type) [Parseable α] -- requires no space for short name, = for long ones
  | required (α : Type) [Parseable α]

def Option.Type (k : Option.Kind) : Type :=
  match k with
  | .none => Bool
  | Kind.optional α => α
  | Kind.required α => α

def Option.TypeParseable (k : Option.Kind) : (α : Type) × (Parseable α) :=
  match k with
  | .none => ⟨Bool, inferInstance⟩
  | @Kind.optional α inst => ⟨α, inst⟩
  | @Kind.required α inst => ⟨α, inst⟩

structure Option where
  short : _root_.Option Char
  long : _root_.Option String
  kind : Option.Kind

def valueType (options : List Option) (key : String) : Type :=
  match options with
  | [] => Unit
  | { short, long, kind } :: options =>
    if key.startsWith "--" then
      match long with
      | some opt =>
        if key = s!"--{opt}" then
          Option.Type kind
        else
          valueType options key
      | none => valueType options key
    else if key.startsWith "-" then
      match short with
      | some opt =>
        if key = s!"-{opt}" then
          Option.Type kind
        else
          valueType options key
      | none => valueType options key
    else panic! "Options should start with '-' or '--'."

-- def parser (options : List Option) (args : List String) :


end DCLI
-/


/-!
TODO:
  Option struct with fields:
    - short (option char),
    - long (option string),
    - at least one of them being not none
    - a valueType,

And create a CLI parser from a list of options that returns a hash map.
What are the values? Last or list? (Mmm, list..., post-process if needed)

TODO: support "--"



-/
