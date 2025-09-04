inductive Block where
| text (string : String)
| code (string : String)
deriving Repr

def openMarkdown := "/-"
def closeMarkdown := "-/"

def flush (as : String -> Block) (blocks : List Block) (buffer: List String) :
  List Block × List String :=
  if !buffer.isEmpty then
    let block := buffer |>.reverse |> "\n".intercalate |> as
    let blocks := block :: blocks
    let buffer := []
    (blocks, buffer)
  else
    (blocks, buffer)

def parse (source : String) : List Block := Id.run do
  let lines := source.splitOn "\n"
  let mut blocks : List Block := []
  let mut buffer : List String := []
  for line in lines do
    if line == openMarkdown then
      (blocks, buffer) := flush (as := Block.code) blocks buffer
    else if line == closeMarkdown then
      (blocks, buffer) := flush (as := Block.text) blocks buffer
    else
      buffer := line :: buffer
  (blocks, _) := flush (as := Block.code) blocks buffer
  return blocks.reverse

def cleanUp (blocks : List Block) : List Block :=
  match blocks with
  | [] => []
  | (.text string) :: rest => (.text string) :: (cleanUp rest)
  | (.code string) :: rest =>
    let string := string.trim
    if string.isEmpty then
      cleanUp rest
    else
      (.code string) :: cleanUp rest

def toMarkdown (blocks : List Block) : String := Id.run do
  let mut markdown := ""
  for block in blocks do
    match block with
    | .text string => markdown := markdown ++ "\n" ++ string ++ "\n"
    | .code string => markdown := markdown ++ "\n```lean\n" ++ string ++ "\n```\n"
  return markdown

def main (args : List String) : IO Unit := do
  let fileName := args[0]!
  let file <- IO.FS.Handle.mk fileName .read
  let source <- file.readToEnd
  let md := source |> parse |> cleanUp |> toMarkdown
  let file <- IO.FS.Handle.mk (fileName ++ ".md") .write
  file.write md.toUTF8
