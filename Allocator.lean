-- Linear Memory Allocation in a 16-bit Address Space

/-
Note: Many interesting properties of our implementation that we could prove
here:

  - That the pointers in the free list is "ordered"

  - That the free list and used list exactly complement each other

  - That the compaction results in a free list without contiguous blocks

  - etc.
-/

abbrev Byte := UInt8

abbrev Pointer := UInt16
-- There is no "null" pointer in this context, so we use 0 as the base pointer.
-- Failure is described by Option types

abbrev Size := UInt16

abbrev Block := Pointer × Size

abbrev Blocks := List Block

abbrev Memory := Vector Byte (2^16)

structure Allocator where
  memory:  Memory := Vector.replicate (2^16) (0 : Byte)
  freeList : Blocks := [(0, (2^16 - 1).toUInt16)]
  usedList : Blocks := []
deriving Repr

-- TODO: actually allow to read/write into the memory? Or direct access via .memory?
--       Yay, that's simpler after all ...

-- Find the first free block in the memory large enough to contain the requested number of Bytes.
-- Return before, current and after blocks (maybe stupid, we could just do a List.find afterwards).
-- Dunno. Keep it like that ATM.
def findFreeBlock (allocator : Allocator) (size: Size) : Option (Blocks × Block × Blocks) := do
  let freeList := allocator.freeList
  guard freeList.isEmpty
  let mut before : Blocks := []
  let mut current_and_after : Blocks := freeList
  while !current_and_after.isEmpty do
    let (ptr, freeSize) := current_and_after.head!
    if size <= freeSize then
      return (before.reverse, current_and_after.head!, current_and_after.tail!)
    else
      before := (ptr, freeSize) :: before
      current_and_after := current_and_after.tail!
  none -- failure

partial def Allocator.malloc (allocator : Allocator) (size: Size) : Option (Pointer × Allocator) := do
  if size == 0 then
    return (0, allocator) -- No allocation needed for size 0
  let (before, current, after) <- findFreeBlock allocator size
  let (ptr, freeSize) := current
  let newBlock := (ptr + size, freeSize - size)
  let newFreeList := before ++ [newBlock] ++ after
  let newUsedList := (ptr, size) :: allocator.usedList
  let newAllocator := { allocator with freeList := newFreeList, usedList := newUsedList }
  return (ptr, newAllocator)

partial def Allocator.free (allocator : Allocator) (ptr: Pointer) : Option Allocator := do
  sorry

-- Compact contiguous free blocks in allocator.
partial def Allocator.compact (allocator : Allocator) : Allocator :=
  let freeList := allocator.freeList
  -- used a foldl here?
  let rec compactBlocks (blocks : Blocks) (acc : Blocks) : Blocks :=
    match blocks with
    | [] => acc.reverse
    | (ptr, size) :: rest =>
      match acc with
      | [] => compactBlocks rest [(ptr, size)]
      | (lastPtr, lastSize) :: lastRest =>
        if lastPtr + lastSize == ptr then
          compactBlocks rest ((lastPtr, lastSize + size) :: lastRest)
        else
          compactBlocks rest ((ptr, size) :: acc)
  let newFreeList := compactBlocks freeList []
  { allocator with freeList := newFreeList }
