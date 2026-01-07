import Std.Data.HashMap

/-!
Wild ideas:

  - do something with "Thing Explainer",

  - use some populat Wikipedia samples to build a dictionary?

  - use some BPE (byte-pair encoding) to get tokens instead of the
    "split on space" strategy to get words?

-/

/-!

Huffman codes

- [X] Define a naive binary coding tree as a classic Tree with String payload,
  and "" which encodes for nothing (conventionally). Nothing is correct by
  construction (for example the prefix-free property is not enforced by the
  compiler), and we will allow some panics if something goes wrong down the
  line. Nota: we could use Option String instead of the "" convention but
  we are so far from being correct by construction that it changes very little.
  But the other option is legitimate, of course. Even if our mental model is
  Python, None or str would make more sense that the sentinel convention,
  which is more C-like in spirit. Well, do both if required.

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


namespace Huffman_0

inductive Tree where
| nil : Tree
| node : String → Tree → Tree → Tree
deriving BEq

/-
I would appreciate having a code (as a hash), an algorithm that decides if
the code is a prefix code, and under this condition turn it into a Huffman
Tree (yeah that's not how it really works since we would start from the
probas, get the tree and thus the prefix-free nature for free, but that would
be convenient nonetheless).
-/

def spoon : Tree :=
  .node ""
    (.node "" -- 0
      (.node "" -- 00
        (.node "-" .nil .nil) -- 000
        (.node "" -- 001
          (.node "" -- 0010
            (.node "[" .nil .nil) -- 00100
            (.node "" -- 00101
              (.node "." .nil .nil) -- 001010
              (.node "" -- 001011
                (.node "," .nil .nil) -- 0010110, read
                (.node "" -- 0010111
                  (.node "d" .nil .nil) -- 00101110, dump memory
                  (.node "x" .nil .nil) -- 00101110, exit
                )
              )
            ) -- 00101
          )
          (.node "]" .nil .nil) -- 0011, end loop
        )
      )
      (.node "" -- 01
        (.node ">" .nil .nil) -- 010, move right
        (.node "<" .nil .nil) -- 011, move left
      )
    )
    (.node "+" .nil .nil) -- 1, increment


-- TODO: make something that stops at the first non-empty string and
--       returns the remaining bools. Panic is not GREAT. We may
--       panic when the bools cannot be interpreted as a proper path
--       but to have the stream decoded, we need to intercept the
--       "the path is not incorrect, but it does not end up in a leaf".
--       And BAM, again we need to have a combination of option and
--       state!
def Tree.decode
    (tree : Tree) (bools : List Bool) : Option (String × List Bool) :=
  match tree with
  | nil => panic! "Decoding error" -- invalid bool path (or tree)
  | node string left right =>
    if string != "" then
      some (string, bools)
    else
      match bools with
      | [] => none -- The bool path is valid so far, but we didn't reach a token.
      | false :: bools => decode left bools
      | true :: bools => decode right bools


#eval spoon.decode []
-- none
#eval spoon.decode [false]
-- none
#eval spoon.decode [false, false]
-- none
#eval spoon.decode [false, false, false]
-- some ("-", [])
#eval spoon.decode [false, false, false, false]
-- som ("-", [false])
#eval spoon.decode [false, false, false, false]
-- som ("-", [false, false])
#eval spoon.decode [false, true, false]
-- some (">", [])


/-
I have used the fixpoint style of implementation which is probably neither
idiomatic not obvious to the beginner. A recursive `decodeLoop` without the
fixpoint abstraction defined inside `decodeStream` would be a simpler first
step. That would also suppress the need for the `step` function (`decodeLoop`
does everything`). And then, *afterwards*, show the fixpoint structure?
-/

/-
Note: the other option is the monadic approach with `do`. Probably many
options here: start to work with the `Id` monad (use `Id.run do`),
just to get mutable structures and whil loops, then afterwards,
see that we actually have a state Monad and use that?
-/

partial def fixpoint {α} [BEq α] (f : α → α) (initial : α) : α :=
  let next := f initial
  if next == initial then
    initial
  else
    fixpoint f next

def Tree.decodeStream
    (tree : Tree) (bools : List Bool) :
    (List String) × (List Bool) :=
  -- adapt `tree.decode` to be used in a fixed-point
  let step (tokens_bools : (List String) × (List Bool)) :
      (List String) × (List Bool) :=
    let (tokens, bools) := tokens_bools
    match tree.decode bools with
    | none => (tokens, bools)
    | some (token, bools) => (tokens ++ [token], bools)
  fixpoint step ([], bools)

#eval spoon.decodeStream [false]
-- ([""], [false])
#eval spoon.decodeStream [false, true]
-- ([], [false, true])
#eval spoon.decodeStream [false, true, false]
-- ([], [false, true])
#eval spoon.decodeStream [false, true, false, false]
-- ([">"], [false])
#eval spoon.decodeStream [false, true, false, false, false]
-- ([">"], [false, false])
#eval spoon.decodeStream [false, true, false, false, false, false]
-- ([">", "-"], [])





instance {α β} [Repr α] [Repr β] [BEq α] [Hashable α] :
  Repr (Std.HashMap α β) where
    reprPrec m _ := repr m.toList

abbrev HashMap := Std.HashMap String (List Bool)

def Tree.hashmap_aux
    (tree : Tree) (path : List Bool) (hashmap : HashMap) : HashMap :=
  match tree with
  | nil => panic! "Invalid path or tree"
  | node string left right =>
    hashmap
      |> fun hm => if string == "" then hm else hm.insert string path
      |> fun hm => if left == nil then hm else left.hashmap_aux (path ++ [false]) hm
      |> fun hm => if right == nil then hm else right.hashmap_aux (path ++ [true]) hm

def Tree.hashmap (tree : Tree) : HashMap :=
  tree.hashmap_aux [] Std.HashMap.emptyWithCapacity

-- Panics if the key is not found.
def Tree.encode (tree : Tree) (string : String) : List Bool :=
  tree.hashmap[string]!

end Huffman_0

-- end Huffman
