/-!
Title : 50 shades of grey

Some functions may not "work properly" for some values.
In pure FP, "errors" are out-of-domain arguments provided by the
developer(/user). How do we deal with this? Many options

- Undefined behavior: document, promise NOTHING if used outside the function
domain (panic, program corruption, infinite loop, etc. all that is fair)

- "junk" / default / fallback  value (sometimes user provided)

- panic!

- sentinel value (Python: -1 in str.find, None in dict.get, etc.)

- Option (/Except)

- Props to avoid inputs outside the function domain (guarantee of no error).

-/

#print Except

/-!
Examples :

  - Array access: []!, [].getD, []?, [] (or []'h)

  - Float.log (-1.0)

  - 1 - 2

  - String.front

  - String.take, String.

-/
