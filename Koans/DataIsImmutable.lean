
/-!
TODO: example in Python of "classic mutable data" : lists, with "prepend"
(aka insert 0) : [1, 2, 3] -> [0, 1, 2, 3]. Two APIs actually: insert or
in-place. They differ! explain identity and show what the difference is.

Show that in-place API may be "dangerous", "difficult to handle", when
the same argument is reused. Documentation and good practices matter!

Example of a snake code (list of pairs with coords) that "moves" in
one direction but is actually invalid because of this?

Example of "classic immutable data": strings. Simple example of the API?
-/

/-!
Mixed case: tuple ; to some extent, it is immutable (see the API and how
some operations raise exceptions). But if you put lists in tuple, you
can change the result of a call to `repr`... So not immutable.



Explanation: as a structure that has *pointers* to its content, its
immutable. *Pointers* characterize objects identity in Python
(TODO: example of the API). So how can we have something different
with `repr`? To interpret pointers (derefence the objects in a tuple),
repr needs to read the memory. So repr is not really a function that
associates to an object a string, it also as the memory mapping of
all Python objects as a second, implicit argument!

The value of the implicit argument can change, so can the output.
-/

/-!
In Lean, every data is immutable. Familiar example with strings,
then show how that works for lists (prepend), with the new list
given as an output.
-/

/-!
There is no identity! No access to locations, *much* simpler:
Values can be "shared", used by several pieces of code, but since none
of them
-/
