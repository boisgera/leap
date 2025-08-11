
-- There are only two kinds of languages:
inductive LanguageKind where
  | onePeopleComplainAbout
  | oneNobodyUses


inductive N where
  | z : N
  | s (n : N) : N -- or s : N -> N
deriving Repr -- Ah, funny, ToString is derived by default, not Repr
-- and this is required for the recursive representation to work AFAICT.

#eval N.z

#eval N.s N.z

#eval N.s (N.s N.z)

inductive L where
  | n : L
  | c (h : N) (t : L) : L -- or c : N -> L -> L

#eval L.n

#eval L.c (N.z) (L.n)

#eval L.c (N.s N.z) (L.c (N.z) (L.n))

inductive T where
  | l (n : N) : T
  | b (l: T) (r : T) : T -- or b : T -> T -> T

#eval T.l (N.z)

#eval T.b (T.l (N.z)) (T.l (N.s N.z))

-- Now renaming types and constructors!
