-- TODO: "du"-like cli in Lean

-- Warning: given the API, the prg will fuck up if the paths are not valid utf-8
-- (which is perfectly legit ...)



-- Step 1: get path as a single arg, display path: size (in bytes),
-- return "success error code"

-- Step 1.5 : error and abort with an appropriate error message and code if the file doesn't exist
-- (don't panic)

-- Step 2: if 0 args display help and success; if > 1 args display help and error code

-- Step 3: if the root path is a directory, also display the list of path/size
-- of its (immediate) children, after a "  " indent. Stay like before if its
-- a file.

/-
Step 4: make this stuff recursive.A helper recursive function would help;
we suggest: `def displayFileSize (path : String) (indent : Nat := 0): IO Unit`
-/

/-
Step 5: display the cumulative size of the directory and its children instead of
its own size (4096). Hint: make a tree structure that gather all information
you need (IO fct), then another one to display what you need. It's cleaner
anyway. I suggest:

  inductive Tree where
  | file : FilePath -> IO.FS.Metadata -> Tree
  | dir : FilePath -> IO.FS.Metadata -> List Tree -> Tree

(YMMV)
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

-- Metadata could be IO.FS.Metadata or simply the size, etc.
inductive Tree (Metadata : Type) where
| file : IO.FS.DirEntry -> Metadata -> Tree Metadata
| dir : IO.FS.DirEntry -> Metadata -> List (Tree Metadata) -> Tree Metadata

partial def getTree (path : FilePath): IO (Tree IO.FS.Metadata) := do
  let entry : IO.FS.DirEntry := {root := path, fileName := ""}
  let metadata <- FilePath.metadata path
  let pathIsFile := !(<- FilePath.isDir path)
  if pathIsFile then
    return Tree.file entry metadata
  else
    let children <- FilePath.readDir path
    let childTrees <- children.mapM (fun child => getTree (FilePath.join child.root child.fileName))
    return Tree.dir entry metadata childTrees.toList

-- namespace Symbol

-- def L := '└'
-- def T := '┬'

-- def I := '│'

-- def dsd := '├'
-- def horizontal := '─'

-- end Symbol

partial def columnLayout (columns : List String) (gutter := 0) : String :=
  match columns with
  | [col1, col2]    => Id.run do
    let mut lines1 := col1.splitOn "\n"
    let mut lines2 := col1.splitOn "\n"
    let m := max lines1.length lines2.length
    lines1 := lines1 ++ (List.replicate (m - lines1.length) "")
    lines2 := lines2 ++ (List.replicate (m - lines2.length) "")
    let n := List.foldl (fun m line => max m line.length) 0 lines1

    sorry
  | []              => ""
  | [col1]          => col1
  | col1 :: cols    => columnLayout [col1, columnLayout cols]

def tree (path : String) : IO String := do
  let path := FilePath.mk path
  let mut children : List String := []
  if (<- path.isDir) then
      let entries <- path.readDir
      children := List.map (·.path.toString) entries.toList
  return ""

def DirEntry.ofFilePath (path : FilePath) : DirEntry :=
  let sep := FilePath.pathSeparator.toString
  match path.components with
  | []           => { root := ".", fileName := "" }
  | [ fileName ] => { root := ".", fileName := fileName }
  | root :: cpts => { root, fileName := sep.intercalate cpts}



end FS


def main (args : List String) : IO UInt32 := do
  match args with
  | [] => help; return 0
  | [path] =>
    if !(<- FilePath.pathExists path) then
      -- when trying panic! uncaught exception: (`Inhabited.default` for `IO.Error`)
      -- Investigate!
      IO.eprintln s!"File not found: {path}"
      return 1
      -- Happy path:
    displayFileSize path
    return 0
  | _ => help; return 1
