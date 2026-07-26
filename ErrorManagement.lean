/-!
Some functions may not "work properly" for some values.
How do we deal with this?

- Undefined behavior: document, promise NOTHING if used outside the function
domain (panic, program corruption, infinite loop, etc. all that is fair)

- panic!

- "junk" / default value

- sentinel value

- Option

- Props to avoid inputs outside the function domain (guarantee of no error).

-/
