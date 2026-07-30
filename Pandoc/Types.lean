/-
  Lean 4 port of `Text.Pandoc.Definition` (pandoc-types-1.23.1.2).

  Translation conventions used throughout:
  * `Data.Text`            ↦ `String`
  * `Int`                  ↦ `Int` (pandoc uses `Int`, not a fixed-width type)
  * `Double`               ↦ `Float`
  * Haskell tuples         ↦ Lean products (`A × B`, right-nested for 3-tuples)
  * `newtype X = X τ`      ↦ a one-field `structure` (gives you `.mk`/`.run`-style
                              access and keeps the type distinct from `τ`)
  * `Data.Map Text v`      ↦ `Std.HashMap String v` (any ordered/assoc map works
                              just as well if you don't have Std/Batteries available;
                              swap this alias out if you'd rather use `Lean.RBMap`
                              or a plain `List (String × v)`)
  * Mutually recursive Haskell ADTs (`Block`/`Inline`/`Citation`/table pieces/
    `MetaValue` all refer to each other) ↦ a single Lean `mutual inductive` block.
  * Record-style constructors (`Citation { .. }`) ↦ Lean `structure`, but since
    `Citation` sits inside the `Inline`/`Block` recursion it has to be declared
    as an `inductive` with named-field-style accessor defs instead (a
    `structure` can't be mixed into a `mutual` block with `inductive`s).

  Derives: only `Repr`/`BEq`/`Inhabited` are added where cheap; add `DecEq`,
  `Ord`, etc. as needed for your proofs.
-/

/-- A minimal string-keyed map alias. Swap for `Lean.RBMap String v compare`
    or `List (String × v)` if you don't want the `Std`/`Batteries` dependency. -/
abbrev StrMap (v : Type) := Std.HashMap String v

/-- `type Target = (Text, Text)` — (URL, title). -/
abbrev Target := String × String

/-- `type Attr = (Text, [Text], [(Text, Text)])` — (id, classes, key-value pairs). -/
abbrev Attr := String × List String × List (String × String)

def nullAttr : Attr := ("", [], [])

/-- `newtype Format = Format Text` -/
structure Format where
  unFormat : String
  deriving Repr, BEq, Inhabited

/-- `data ListNumberStyle` -/
inductive ListNumberStyle where
  | defaultStyle
  | example
  | decimal
  | lowerRoman
  | upperRoman
  | lowerAlpha
  | upperAlpha
  deriving Repr, BEq, Inhabited

/-- `data ListNumberDelim` -/
inductive ListNumberDelim where
  | defaultDelim
  | period
  | oneParen
  | twoParens
  deriving Repr, BEq, Inhabited

/-- `type ListAttributes = (Int, ListNumberStyle, ListNumberDelim)` -/
abbrev ListAttributes := Int × ListNumberStyle × ListNumberDelim

/-- `data Alignment` -/
inductive Alignment where
  | alignLeft
  | alignRight
  | alignCenter
  | alignDefault
  deriving Repr, BEq, Inhabited

/-- `data ColWidth = ColWidth Double | ColWidthDefault` -/
inductive ColWidth where
  | colWidth (w : Float)
  | colWidthDefault
  deriving Repr, Inhabited

/-- `type ColSpec = (Alignment, ColWidth)` -/
abbrev ColSpec := Alignment × ColWidth

/-- `newtype RowHeadColumns = RowHeadColumns Int` -/
structure RowHeadColumns where
  unRowHeadColumns : Int
  deriving Repr, BEq, Inhabited

/-- `newtype RowSpan = RowSpan Int` -/
structure RowSpan where
  unRowSpan : Int
  deriving Repr, BEq, Inhabited

/-- `newtype ColSpan = ColSpan Int` -/
structure ColSpan where
  unColSpan : Int
  deriving Repr, BEq, Inhabited

/-- `data QuoteType` -/
inductive QuoteType where
  | singleQuote
  | doubleQuote
  deriving Repr, BEq, Inhabited

/-- `data MathType` -/
inductive MathType where
  | displayMath
  | inlineMath
  deriving Repr, BEq, Inhabited

/-- `data CitationMode` -/
inductive CitationMode where
  | authorInText
  | suppressAuthor
  | normalCitation
  deriving Repr, BEq, Inhabited

/-
  The core document tree. `Block`, `Inline`, `MetaValue`, `Citation`, and the
  table sub-structures (`Row`, `Cell`, `TableHead`, `TableBody`, `TableFoot`,
  `Caption`) are mutually recursive in pandoc-types, exactly as in Haskell:
  `Block.Table` contains `Caption`/`TableHead`/…, which contain `Row`, which
  contains `Cell`, which contains `List Block` again; `Inline.Cite` contains
  `Citation`, which contains `List Inline`; `Inline.Note` contains `List Block`;
  and `MetaValue` contains both `List Inline` and `List Block`.
-/
mutual

/-- `data MetaValue = MetaMap … | MetaList … | MetaBool … | MetaString … |
      MetaInlines … | MetaBlocks …` -/
inductive MetaValue where
  | map     (m : StrMap MetaValue)
  | list    (xs : List MetaValue)
  | bool    (b : Bool)
  | string  (s : String)
  | inlines (is : List Inline)
  | blocks  (bs : List Block)

/-- `data Block = Plain … | Para … | … | Div …` -/
inductive Block where
  | plain          (content : List Inline)
  | para           (content : List Inline)
  | lineBlock      (lns : List (List Inline))
  | codeBlock      (attr : Attr) (code : String)
  | rawBlock       (format : Format) (content : String)
  | blockQuote     (content : List Block)
  | orderedList    (attrs : ListAttributes) (items : List (List Block))
  | bulletList     (items : List (List Block))
  | definitionList (items : List (List Inline × List (List Block)))
  | header         (level : Nat) (attr : Attr) (content : List Inline)
  | horizontalRule
  | table          (attr : Attr) (caption : Caption) (colSpecs : List ColSpec)
                   (head : TableHead) (bodies : List TableBody) (foot : TableFoot)
  | figure         (attr : Attr) (caption : Caption) (content : List Block)
  | div            (attr : Attr) (content : List Block)

/-- `data Inline = Str … | Emph … | … | Span …` -/
inductive Inline where
  | str         (text : String)
  | emph        (content : List Inline)
  | underline   (content : List Inline)
  | strong      (content : List Inline)
  | strikeout   (content : List Inline)
  | superscript (content : List Inline)
  | subscript   (content : List Inline)
  | smallCaps   (content : List Inline)
  | quoted      (quoteType : QuoteType) (content : List Inline)
  | cite        (citations : List Citation) (content : List Inline)
  | code        (attr : Attr) (text : String)
  | space
  | softBreak
  | lineBreak
  | math        (mathType : MathType) (text : String)
  | rawInline   (format : Format) (text : String)
  | link        (attr : Attr) (content : List Inline) (target : Target)
  | image       (attr : Attr) (content : List Inline) (target : Target)
  | note        (content : List Block)
  | span        (attr : Attr) (content : List Inline)

/-- `data Citation = Citation { citationId :: …, .. }`
    (a record in Haskell; kept as a positional constructor here since it has
    to live inside the `mutual` block — see `citationId` etc. accessors below). -/
inductive Citation where
  | mk (citationId : String)
       (citationPrefix : List Inline)
       (citationSuffix : List Inline)
       (citationMode : CitationMode)
       (citationNoteNum : Nat)
       (citationHash : Nat)

/-- `data Row = Row Attr [Cell]` -/
inductive Row where
  | mk (attr : Attr) (cells : List Cell)

/-- `data Cell = Cell Attr Alignment RowSpan ColSpan [Block]` -/
inductive Cell where
  | mk (attr : Attr) (align : Alignment) (rowSpan : RowSpan) (colSpan : ColSpan)
       (content : List Block)

/-- `data TableHead = TableHead Attr [Row]` -/
inductive TableHead where
  | mk (attr : Attr) (rows : List Row)

/-- `data TableBody = TableBody Attr RowHeadColumns [Row] [Row]`
    (the two row lists are the "head" rows and "body" rows of this body). -/
inductive TableBody where
  | mk (attr : Attr) (rowHeadCols : RowHeadColumns) (headRows : List Row) (bodyRows : List Row)

/-- `data TableFoot = TableFoot Attr [Row]` -/
inductive TableFoot where
  | mk (attr : Attr) (rows : List Row)

/-- `data Caption = Caption (Maybe ShortCaption) [Block]` -/
inductive Caption where
  | mk (short : Option (List Inline)) (long : List Block)

end

-- Field-accessor sugar for `Citation`, mirroring the Haskell record fields.
namespace Citation
def citationId       : Citation → String            | .mk i _ _ _ _ _ => i
def citationPrefix   : Citation → List Inline        | .mk _ p _ _ _ _ => p
def citationSuffix   : Citation → List Inline        | .mk _ _ s _ _ _ => s
def citationMode     : Citation → CitationMode       | .mk _ _ _ m _ _ => m
def citationNoteNum  : Citation → Nat                | .mk _ _ _ _ n _ => n
def citationHash     : Citation → Nat                | .mk _ _ _ _ _ h => h
end Citation

/-- `type ShortCaption = [Inline]` -/
abbrev ShortCaption := List Inline

/-- `newtype Meta = Meta { unMeta :: Map Text MetaValue }` -/
structure Meta where
  unMeta : StrMap MetaValue

def nullMeta : Meta := ⟨{}⟩

def isNullMeta (m : Meta) : Bool := m.unMeta.isEmpty

def lookupMeta (key : String) (m : Meta) : Option MetaValue :=
  m.unMeta.get? key

/-- `data Pandoc = Pandoc Meta [Block]` — the top-level document. -/
inductive Pandoc where
  | mk (meta : Meta) (blocks : List Block)

/-!
`docTitle`, `docAuthors`, `docDate` and the `SimpleFigure` pattern from the
Haskell module are ordinary derived helpers, not part of the core type; a
faithful (if partial) port of `docTitle`/`docDate` would look like:

```
def docTitle (m : Meta) : List Inline :=
  match lookupMeta "title" m with
  | some (.inlines is) => is
  | some (.string s)   => [.str s]
  | some (.blocks (.plain is :: _)) => is
  | some (.blocks (.para  is :: _)) => is
  | _ => []
```

They're omitted here since they depend on `MetaValue`/`Block` case analysis
rather than on the data model itself.
-/
