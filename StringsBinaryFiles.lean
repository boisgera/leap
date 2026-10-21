
#eval IO.println "Hello world!"
-- Hello world!


/-!
Standard IO streams
--------------------------------------------------------------------------------

Let's implement our own `println` function, using an explicit call to the
standard output that we can get from `IO.getStdOut`.
-/

#check IO.getStdout
-- IO.getStdout : BaseIO IO.FS.Stream

#print IO.FS.Stream
-- structure IO.FS.Stream : Type
-- number of parameters: 0
-- fields:
--   IO.FS.Stream.flush : IO Unit
--   IO.FS.Stream.read : USize → IO ByteArray
--   IO.FS.Stream.write : ByteArray → IO Unit
--   IO.FS.Stream.getLine : IO String
--   IO.FS.Stream.putStr : String → IO Unit
--   IO.FS.Stream.isTty : BaseIO Bool
-- constructor:
--   IO.FS.Stream.mk (flush : IO Unit) (read : USize → IO ByteArray) (write : ByteArray → IO Unit) (getLine : IO String)
--     (putStr : String → IO Unit) (isTty : BaseIO Bool) : IO.FS.Stream



namespace My

def println {α} [ToString α] (a: α) : IO Unit := do
  let stdout <- IO.getStdout
  stdout.putStr (toString a ++ "\n") -- ℹ️ alt: use `stdout.putStrln`.

#eval println "Hello world!"
-- Hello world!

/-!
Note: Lean will provide the terminal with a UTF-8 encoded version of strings
(it uses this encoding internally). That will display [mojibake] if your
terminal does not actually use this encoding.

[mojibake]: https://en.wikipedia.org/wiki/Mojibake

To get a lower-level implementation
We can deal directly with the UTF-8 encoding data using `String.UTF8`:
-/

#check String.toUTF8
-- String.toUTF8 (a : String) : ByteArray

#eval "a".toUTF8
-- [97]

#eval "é".toUTF8
-- [195, 169]

#eval "∀".toUTF8
-- [226, 136, 128]]

#eval "🙂".toUTF8
-- [240, 159, 153, 130]


def println' {α} [ToString α] (a: α) : IO Unit := do
  let stdout <- IO.getStdout
  let bytes := (toString a ++ "\n").toUTF8
  stdout.write bytes

#eval println' "Hello world!"
-- Hello world!

/-
Now let's see how to read read data. We can read UTF-8 encoded text content
as a `String`, one line at a time, with the `getLine` method from the standard
input for example.

```lean
def main : IO Unit := do
  IO.print "What is your name? "
  (<- IO.getStdin).flush
  let stdin <- IO.getStdin
  let content <- stdin.getLine
  let name := content.trimAsciiEnd -- get rid of the trailing newline.
  IO.println s!"Hello {name}!"
```
-/

/-
We can also read the contents of the stream as binary data:

```lean
def main : IO Unit := do
  IO.print "Please enter 4 bytes of data and press enter: "
  let stdin <- IO.getStdin
  let binary <- stdin.read 4
  IO.println s!"Binary data: {binary}"
```

Note that an EOF signal, created by CTRL+D allows us to provide less than 4 bytes.

-/

/-!
`ByteArray`
--------------------------------------------------------------------------------
-/

#print ByteArray
-- structure ByteArray : Type
-- number of parameters: 0
-- fields:
--   ByteArray.data : Array UInt8
-- constructor:
--   ByteArray.mk (data : Array UInt8) : ByteArray

/-!
You can create a `ByteArray` from an array of unsigned 8-bit integers
and conversely convert the byte array back.
-/

def array : Array UInt8 := #[0, 127, 255]

def byteArray : ByteArray := ByteArray.mk array

#eval byteArray
-- [0, 127, 255]

#eval ByteArray.mk (#[0, 127, 255] : Array UInt8)
-- [0, 127, 255]

/-!
The difference is that `Array` packs a sequence of Lean object *pointers*,
while `ByteArray` packs the bytes directly, which offers better performance
characteristics.
-/

/-!
The basic ByteArray API:
-/

#check byteArray.size
-- byteArray.size : Nat
#eval byteArray.size
-- 3
#eval byteArray.isEmpty
-- false

/-!
Creation:
-/

#eval ByteArray.empty
-- []
#eval ByteArray.empty.size
-- 0
#eval ByteArray.empty.isEmpty
-- true

#eval ByteArray.emptyWithCapacity 64 -- reserves initial capacity
-- []
#eval ByteArray.emptyWithCapacity 64 |>.size -- the size is still 0
-- 0
#eval ByteArray.emptyWithCapacity 64 |>.isEmpty
-- true

/-!
Access:
-/

#eval byteArray[2]!
-- 255

#eval byteArray[3]!
-- 🫨 PANIC

#eval byteArray[2]?
-- some 255

#eval byteArray[3]?
-- none

#eval byteArray[2]
-- 255

theorem two_lt_array_size : 2 < byteArray.size := by unfold

#eval byteArray[2]'two_lt_array_size

#eval byteArray[3] -- ❌
-- failed to prove index is valid, possible solutions:
--   - Use `have`-expressions to prove the index is valid
--   - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
--   - Use `a[i]?` notation instead, result is an `Option` type
--   - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
-- ⊢ 3 < byteArray.size

/-!
Mutation:
-/

#eval byteArray.push 255
-- [0, 127, 255, 255]

#eval byteArray.set! 0 127
-- [127, 127, 255]

#eval byteArray.set 2 127 two_lt_array_size

/-!
Slicing and joining:
-/

#eval byteArray.extract 1 2
-- [127]

#eval byteArray.extract 0 1 ++ byteArray.extract 2 3
-- [0, 255]

#eval byteArray.copySlice
  (srcOff := 1)
  (dest := ByteArray.mk #[0, 1, 2, 3, 4, 5])
  (destOff := 0)
  (len := 2)
-- [127, 255, 2, 3, 4, 5]

/-!
Iteration:
-/

#eval (
  for elt in byteArray do
  IO.println s!"* {elt}"
)
-- * 0
-- * 127
-- * 255

/-!
Files
--------------------------------------------------------------------------------
-/

def doFiles : IO Unit := do
  -- create (or truncate) a file, UTF-8 encode the string
  IO.FS.writeFile "hello.txt" "Hello world!\n❤️"
  -- read as a String (UTF-8 decoded)
  let string ← IO.FS.readFile "hello.txt"
  IO.println string
  let lines ← IO.FS.lines "hello.txt" -- Array String, one per line
  for line in lines do
    IO.println s!"- {line}"
  IO.FS.writeBinFile "data.bin" "❤️".toUTF8 -- write a byte array
  let bytes ← IO.FS.readBinFile "data.bin"  -- read a byte array
  IO.println s!"❤️ (UTF-8): {bytes}"

#eval doFiles
-- Hello world!
-- ❤️
-- - Hello world!
-- - ❤️
-- ❤️ (UTF-8): [226, 157, 164, 239, 184, 143]

/-!
TODO!: incremental API to read and write, with handles
-/

end My


/-!
Processes
--------------------------------------------------------------------------------
-/

def doProcess : IO Unit := do
  let out ← IO.Process.output { cmd := "echo", args := #["Hello!"] }
  IO.println s!"\
- exit={out.exitCode}
- stdout={repr out.stdout}
- stderr={repr out.stderr}"

  -- like `output`, but throws on non-zero exit and returns just stdout
  let string ← IO.Process.run { cmd := "uname", args := #["-s"] }
  IO.print string

#eval doProcess
