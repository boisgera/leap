/- "du"+"tree" (or "duc")-like cli in Lean

Warning: given the API, the prg will fuck up if the paths are not valid utf-8
(which is perfectly legit ...). Don't worry about it.

Step 0: get path as a single arg, display the filename part of the
absolute version of this path return "success error code".

Step 1 : error and abort with an appropriate error message on stderr and
status code if the path doesn't exist in the file system (don't panic).

Step 2: if 0 args display help and success.

Step 3: if the root path is a directory, also display the list of path/size
of its (immediate) children, after a "  " indent. Stay like before if its
a file.

Step 4: make this stuff recursive, so that we get a nice tree-like display
(the deeper we are, the more indent we have).

Step 5: if you haven't already, instead of putting everything into a IO context,
create:

  - a "file-system tree" data structure (with tuples and lists, and stuff) (no IO),

  - a IO that generate this data structure from a path,

  - a function that generate the appropriate string to represent this as we need.

Integrate all this to get the same feature as Step 4 (but cleaner).

Step 6: replace your ad-hoc data structure with an appropriate inductive type
Tree; make it an instance of ToString. Integrate again.

Step 7: adapt Tree to make it store the file metadata.

Step 8: For each file/dir, add the info about the cumulative side in a left
column (TODO: left pad that stuff to get the right column aligned)

Step 9: make a "byteSize4Humans" function that consistently uses at most 6 chars.
e.g. "8.0B", "4.1K", "990.0G" and use it to display the size!

-/

open IO.FS (DirEntry)
open System (FilePath)

def help : IO Unit :=
  IO.println "Usage: fs <path>"

partial def displayFileSize (path : String) (indent : Nat := 0): IO Unit := do
  let metadata <- FilePath.metadata path
  let indentStr := "".intercalate (List.replicate indent "  ")
  IO.println s!"{indentStr}{path}: {metadata.byteSize}"
  if (<- FilePath.isDir path) then
    let children <- FilePath.readDir path
    for child in children do
        let path := child.root.toString ++ (String.singleton FilePath.pathSeparator) ++ child.fileName
        displayFileSize path (indent + 1)


namespace FS

def indent (string : String) :=
  let lines := string.splitOn "\n"
  let lines := lines.map ("  " ++ ·)
  "\n".intercalate lines

partial def tree_ (path : String) : IO String := do
  let path := FilePath.mk path
  let mut s : String := ""
  let absPath <- IO.FS.realPath path
  s := s ++ absPath.fileName.get! ++ "\n"
  if (<- path.isDir) then
    for child in (<- path.readDir) do
      let childPath := path / child.fileName
      s := s ++ (indent (<- tree_ (toString childPath)))
  return s

-- Structure instead? with empty children for file and additional "type" flag?
inductive Tree where
| file (fileName : String) (metadata : IO.FS.Metadata) : Tree
| dir (fileName : String) (metadata : IO.FS.Metadata) (children : List Tree) : Tree

partial def Tree.ofPath (path : FilePath) : IO Tree := do
  let absPath <- IO.FS.realPath path
  let fileName := absPath.fileName.get!
  if (<- path.isDir) then
    let mut children : List Tree := []
    for child in (<- path.readDir) do
      let childPath := path / child.fileName
      children := children ++ [<- Tree.ofPath childPath]
    return Tree.dir fileName (<- path.metadata) children
  else
    return Tree.file fileName (<- path.metadata)

def Tree.fileName (tree : Tree) : String :=
  match tree with
  | file fileName _ => fileName
  | dir fileName _ _ => fileName

def Tree.metadata (tree : Tree) : IO.FS.Metadata :=
  match tree with
  | file _ metadata => metadata
  | dir _ metadata _ => metadata

def Tree.children (tree : Tree) : List Tree :=
  match tree with
  | file _ _ => []
  | dir _ _ children => children






-- Warning: very inefficient
partial def cumulativeSize (tree : Tree) : UInt64 :=
  tree.metadata.byteSize + (tree.children.map cumulativeSize).sum


def round_1 (f : Float) : Float :=
  f |> (· * 10.0) |>.round |> (· / 10.0)

def units := ["B", "K", "M", "G", "T", "P", "E", "Z", "Y", "R", "Q"]

def byteSize4Humans (size : UInt64) : String := Id.run do
  let mut size := round_1 size.toFloat
  let mut unit := "B"
  let mut i := 0
  while size >= 1000.0 do
    i := i + 1
    unit := units[i]!
    size := round_1 (size / 1000.0)
  let sizeDigits := s!"{(size * 10.0).toUInt64}"
  let frac := sizeDigits.drop (sizeDigits.length - 1)
  let integ := sizeDigits.take (sizeDigits.length - 1)
  return s!"{integ}.{frac}{unit}"

def leftPad  (length : Nat) (string : String) : String := Id.run do
  let mut string := string
  while (string.length < length) do
    string := " " ++ string
  return string

#eval leftPad 6 (byteSize4Humans 5675000675)
-- "  5.7G"

partial def Tree.toString_ (tree : Tree) : String :=
  let root := tree.fileName ++ "\n"
  let children := "".intercalate (tree.children.map (indent ∘ Tree.toString_))
  root ++ children

partial def Tree.getCumulativeByteSizes (tree : Tree) : List UInt64 :=
  let childrenCumulativeSizes := tree.children.flatMap getCumulativeByteSizes
  [tree.metadata.byteSize + (List.sum childrenCumulativeSizes)] ++ childrenCumulativeSizes

partial def Tree.toStringAux (tree : Tree) : String :=
  let root := tree.fileName ++ "\n"
  let children := "".intercalate (tree.children.map (indent ∘ Tree.toStringAux))
  root ++ children

partial def Tree.toString (tree : Tree) : String :=
  let rightColumn := tree.toStringAux.splitOn "\n"
  let leftColumn := tree.getCumulativeByteSizes.map (· |> byteSize4Humans |> leftPad 6)
  let lines := (List.zip leftColumn rightColumn).map (fun (l, r) => l ++ " " ++ r)
  -- "\n".intercalate lines
  "\n".intercalate lines

instance : ToString Tree where
  toString := Tree.toString

end FS


def main (args : List String) : IO UInt32 := do
  match args with
  | [] => help; return 0
  | [path] =>
    if !(<- FilePath.pathExists path) then
      IO.eprintln s!"File not found: {path}"
      return 1
    IO.println (<- FS.Tree.ofPath path)
    return 0
  | _ => help; return 1
