/-!

TODO: Huffman codes:


- [X] Define a "naive^2" Huffman tree with String payload, "" encodes for nothing

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


inductive Tree where
  | nil : Tree
  | leaf
      (string? : Option String)
      (left : Tree)
      (right : Tree)
      (check : string?.isSome → (left = Tree.nil) ∧ (right = Tree.nil)) :
      Tree



-- def Tree.decode (tree : Tree) (bools : List Bool) : Option String :=
--   match bools with
--   | [] =>
--     match tree with
--     | nil => none
--     |
--   | b :: bools => sorry

-- end Huffman
