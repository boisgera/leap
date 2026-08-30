import Lean
open Lean (Json JsonNumber)

-- import Std

-- def memoize {α β} [BEq α] [Hashable α] (f : α -> β) (a : α) :
--       (Std.HashMap α β) -> β × (Std.HashMap α β) :=
--     fun cache => match cache.get? a with
--       | some b =>
--         (b, cache)
--       | none =>
--         let b := f a
--         (b, cache.insert a b)


/-
Text Index
--------------------------------------------------------------------------------
-/

def find (text word : String) : List Nat :=
  let chars := text.toList
  let subChars := word.toList
  let indices := List.range text.length
  let matchAt (i : Nat) : Bool :=
    subChars == (chars |>.drop i |>.take subChars.length)
  indices.filter matchAt


abbrev Index := Std.HashMap String (List Nat)

def mkIndex (text : String) (words : List String) : Index :=
  words.foldl (init := {})
      fun index word  =>
        index.insert word (find text word)

def main1 (args : List String) : IO Unit := do
  let filename := args[0]!
  let text <- IO.FS.readFile filename
  let words := args.drop 1
  let index := mkIndex text words
  IO.println (repr index)

def findWithIndex (text word : String) (index : Index) : (List Nat) × Index :=
  match index.get? word with
  | some indices => (indices, index)
  | none =>
    let indices := find text word
    (indices, index.insert word indices)

def mkIndex' (text : String) (words : List String) : Index :=
  words.foldl (init := ({} : Index))
      fun index word  =>
        let (_, new_index) := findWithIndex text word index
        new_index

def main2 (args : List String) : IO Unit := do
  let filename := args[0]!
  let text <- IO.FS.readFile filename
  let words := args.drop 1
  let index := mkIndex' text words
  IO.println (repr index)

def findSome (text : String): List (List Nat) :=
  let indices1 := find text "to"
  let indices2 := find text "be"
  let indices3 := find text "or"
  let indices4 := find text "not"
  let indices5 := find text "to"
  let indices6 := find text "be"
  [indices1, indices2, indices3, indices4, indices5, indices6]

def findSomeWithIndex (text : String) (index : Index) :
    (List (List Nat) × Index) :=
  let (indices1, index) := findWithIndex text "to" index
  let (indices2, index) := findWithIndex text "be" index
  let (indices3, index) := findWithIndex text "or" index
  let (indices4, index) := findWithIndex text "not" index
  let (indices5, index) := findWithIndex text "to" index
  let (indices6, index) := findWithIndex text "be" index
  (
    [indices1, indices2, indices3, indices4, indices5, indices6],
    index
  )

def findSomeList (text : String) : List (List Nat) :=
  let words := "to be or not to be".splitOn " "
  words.map (find text ·)

def findSomeListWithIndex (text : String) (index : Index) :
    (List (List Nat) × Index) :=
  let words := "to be or not to be".splitOn " "
  let result : (List (List Nat) × Index) :=
    words.foldl
      (init := ([], index))
      fun (positionsList, index) word =>
        let (positions, newIndex) := findWithIndex text word index
        (positions :: positionsList, newIndex)
  (result.1.reverse, result.2)

/-!
TODO: the missing step: do them with "pure" and "bind" without do sugar.
-/

def findSomeWithIndexStateMDoSyntax (text : String) : StateM Index (List (List Nat)) := do
  let indices1 <- findWithIndex text "to"
  let indices2 <- findWithIndex text "be"
  let indices3 <- findWithIndex text "or"
  let indices4 <- findWithIndex text "not"
  let indices5 <- findWithIndex text "to"
  let indices6 <- findWithIndex text "be"
  return [indices1, indices2, indices3, indices4, indices5, indices6]

/- After that raw, hard higher-order version, do the same stuff with do tricks -/
def findSomeListWithFunctionsOfTheIndex (text : String) :
    Index -> List (List Nat) × Index :=
  let words := "to be or not to be".splitOn " "

  -- That one hurt my brain.
  let indicesList : Index -> List (List Nat) × Index := words.foldl
    (init := fun index => ([], index))
    (fun state word =>
      fun initIndex =>
        let (indicesList, index) := state initIndex
        let (indices, newIndex) := findWithIndex text word index
        (indices :: indicesList, newIndex)
    )

  let reverse {α} (listM : Index -> (List α) × Index)
      : Index -> (List α) × Index :=
    fun index =>
      let (list, newIndex) := listM index
      (list.reverse, newIndex)

  reverse indicesList

/-
Use the monad type shortcut AND refactor the pieces using do ;
the first step is interesting in its own right.
-/

abbrev m := StateM Index -- i.e fun α => Index -> α × Index


def findSomeListWithIndexStateMDoSyntax (text : String) : m (List (List Nat)) :=
  let words := "to be or not to be".splitOn " "

  let indicesList : m (List (List Nat)) := words.foldlM
    (init := [])
    fun indicesList word => do
      let indices <- findWithIndex text word
      return indices :: indicesList

  let reverse {α} (listM : m (List α)) : m (List α) := do
    let list : List α <- listM
    return list.reverse

  reverse indicesList
  -- return (<- indicesList).reverse would also have worked!

def findSomeListWithIndexStateMDoSyntaxAndMutAndForLoops (text : String) : StateM Index (List (List Nat)) := do
  let words := "to be or not to be".splitOn " "
  let mut indicesList : List (List Nat) := []
  for word in words do
    indicesList := (<- findWithIndex text word) :: indicesList
  return indicesList.reverse

/-!
TODO: findSomeListWithIndexStateM
-/
def main3 : IO Unit := do
  let hamlet <- IO.FS.readFile "Hamlet.txt"
  findSome hamlet |> IO.println
  findSomeWithIndex hamlet {} |>.1 |> IO.println
  findSomeList hamlet |> IO.println
  findSomeListWithIndex hamlet {} |>.1 |> IO.println

  findSomeWithIndexStateMDoSyntax hamlet {} |>.1 |> IO.println
  findSomeListWithIndexStateMDoSyntax hamlet {} |>.1 |> IO.println

def main := main3

  -- TODO: generate as <FILENAME>.index?

  -- let json := Json.mkObj (index.map (fun (word, positions) =>
  --   (word, Json.arr (positions.map (Json.num ∘ JsonNumber.fromNat)).toArray)))
  -- IO.println json
