-- Linear Memory Allocation in a 16-bit Address Space

/-
Note: many interesting properties that we could prove here:

  - That the pointers in the free list is "ordered"

  - That the free list and used list exactly complement each other

  - That the compaction results in a free list without contiguous blocks

  - etc.
-/

abbrev Byte := UInt8

abbrev Pointer := UInt16
-- There is no "null" pointer in this context, so we use 0 as the base pointer.
-- Failure is described by Option types

abbrev Size := UInt32 -- we need up to 2^16, not 2^16-1 ...
-- Unless we purposedly describe blocks as "(ptr, size - 1)", then we can
-- deal with only UInt16 integers. Apart from the care that we then have
-- to take with arithmetic, we would probably need to patch the representation
-- of blocks to make them more palatable (readable).
-- Then Blocks would probably be better as a new type (structure) ?
-- OR, make blocks describe (first, last), that works too.

abbrev Block := Pointer × Size

abbrev Blocks := List Block

-- abbrev Memory := Vector Byte (2^16)

structure Allocator where
  -- memory:  Memory := Vector.replicate 2^16 (0 : Byte)
  freeList : Blocks := [(0, 2^16)] -- sorted by first argument (ptr)
  usedList : Blocks := [] -- could/should we use a HashMap instead?
deriving Repr

-- TODO: actually allow to read/write into the memory? Or direct access via .memory?
--       Yay, that's simpler after all ... But then the allocator doesn't NEED
--       to manage the memory, just the free and used lists info.
--

-- Find the first free block in the memory large enough to contain the requested number of Bytes.
-- Return before, current and after blocks (maybe stupid, we could just do a List.find afterwards).
-- Dunno. Keep it like that ATM.
def Allocator.findFreeBlock (allocator : Allocator) (size: Size) : Option (Blocks × Block × Blocks) := do
  let freeList := allocator.freeList
  guard !freeList.isEmpty
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

def Allocator.alloc (allocator : Allocator) (size: Size) : Option (Pointer × Allocator) := do
  if size == 0 then
    return (0, allocator) -- No allocation needed for size 0
  let (before, current, after) <- findFreeBlock allocator size
  let (ptr, freeSize) := current
  let newFreeBlocks := if (size < freeSize) then
    -- chop the first free block on the left
    [(ptr + size.toUInt16, freeSize - size)]
  else
    [] -- perfect fit, remove the free block entirely
  let freeList := before ++ newFreeBlocks ++ after
  let usedList := (ptr, size) :: allocator.usedList
  return (ptr, { allocator with freeList, usedList })


-- Compact contiguous free blocks in allocator.
-- Note: the name "compact" is a bit misleading, as it does not actually
-- MOVE the memory, just collapses adjacent blocks in the free list.
partial def Allocator.compact (allocator : Allocator) : Allocator :=
  let freeList_reversed := allocator.freeList.foldl (init := [])
    fun (acc : Blocks) (block : Block) =>
      match acc with
      | [] => [block] -- first block, just add it
      | (prevPtr, prevSize) :: rest =>
        let (ptr, size) := block
        if (prevPtr.toUInt32 + prevSize = ptr.toUInt32) then
          -- merge with previous block
          (prevPtr, prevSize + size) :: rest
        else
          -- keep as separate block
          block :: acc
  { allocator with freeList := freeList_reversed.reverse }

def sortBlocks (blocks : Blocks) : Blocks :=
  blocks.mergeSort (·.1 < ·.1)

partial def Allocator.free (allocator : Allocator) (ptr: Pointer) : Option Allocator := do
  let freeList := allocator.freeList
  let usedList := allocator.usedList
  let block <- usedList.find? (·.1 == ptr)
  let usedList := usedList.filter (· != block)
  let freeList := (block :: freeList) |>.mergeSort (·.1 < ·.1)
  return { allocator with freeList, usedList }.compact

def allocator : Allocator := {}

#eval allocator.alloc 0

#eval allocator.findFreeBlock 1024

#eval allocator.alloc 1024

#eval do
  let (ptr₁, allocator) <- allocator.alloc 512
  let (ptr₂, allocator) <- allocator.alloc 512
  let (_, allocator) <- allocator.alloc 1024
  let allocator <- allocator.free ptr₁
  let allocator <- allocator.free ptr₂ -- autocompact
  return allocator
-- some {
--   freeList := [(0, 512), (512, 512), (2048, 63488)],
--   usedList := [(1024, 1024)]
-- }
