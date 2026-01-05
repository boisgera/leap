import Std.Data.HashMap

/-!

TODO: Huffman codes:


- [X] Define a "naive^2" Huffman tree with String payload, "" which
  encodes for nothing (conventionally). Nothing is correct by construction,
  and we will allow some panics if something goes wrong down the line

- [X] `Tree.decode` that works on list of bools and panics when needed.

- [X] Huffman tree to hash map (string to bools) computation.

- [X] "Patch" with String -> Option String
  (still naive since it does not encode the fact that only terminal trees can
  carry a String)

- [ ] Improve the tree, make it correct/valid by construction. (Nota : is there a
  way to to that without using props? Only with ADTs? Mmm there kind of is
  with a third node type "terminal" but then there we would allow 2 kinds
  of terminal nodes, some without payload ; can we do something with no
  nil, left node, right node, full node and terminal? Probably)

- [ ] Huffman decoder

- [ ] Find some text corpora, tokenize it, compute the probabilities of each word.


- [ ] Import/Export this tree from JSON?

- [ ] Flat (hashmap) representation of a Huffman tree

- [ ] Huffman encoder (need a tree to flat representation first?)

-/


-- namespace Huffman

/- Not great here : -/


-- inductive Tree where
-- | nil : Tree
-- | leaf
--     (string? : Option String)
--     (left : Tree)
--     (right : Tree)
--     (check : string?.isSome → (left = Tree.nil) ∧ (right = Tree.nil)) :
--     Tree

/-
inductive Tree : Bool → Type where
  | nil : Tree true
  | leaf
      (string? : Option String)
      {lisNil risNil}
      (left : Tree lisNil)
      (right : Tree risNil)
      (check : string?.isSome → lisNil ∧ risNil) :
      Tree false
-/

/-
-- Pretty good, *except* that pseudo-leaves without string payloads exist
inductive Tree where
| nil : Tree
| branch : Tree → Tree → Tree
| leaf : String → Tree
-/

/-!
Let's start with the naive stuff, right? Conventionally, String = "" means
"no payload" and the fact that payload appear only when the node is terminal
is *not* given by construction.
-/

namespace Huffman_1

inductive Tree where
| nil : Tree
| node : String → Tree → Tree → Tree
deriving BEq

abbrev Bools := List Bool

def Tree.decode (tree : Tree) (bools : Bools) : String :=
  match tree with
  | nil => panic! "Decoding error"
  | node string left right =>
    match bools with
    | [] => string
    | false :: bools => decode left bools
    | true :: bools => decode right bools


instance {α β} [Repr α] [Repr β] [BEq α] [Hashable α] :
  Repr (Std.HashMap α β) where
    reprPrec m _ := repr m.toList

abbrev HashMap := Std.HashMap String (Bools)

def Tree.hashmap_aux
    (tree : Tree) (path : Bools) (hashmap : HashMap) : HashMap :=
  match tree with
  | nil => panic! "Invalid path or tree"
  | node string left right =>
    hashmap
      |> fun hm => if string == "" then hm else hm.insert string path
      |> fun hm => if left == nil then hm else left.hashmap_aux (path ++ [false]) hm
      |> fun hm => if right == nil then hm else right.hashmap_aux (path ++ [true]) hm

def Tree.hashmap (tree : Tree) : HashMap :=
  tree.hashmap_aux [] Std.HashMap.emptyWithCapacity

-- TODO: encode

end Huffman_1

-- end Huffman
