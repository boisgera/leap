-- Linear Memory Allocation on a 16-bit memory space

/-
Note: many interesting properties that we could prove here:

  - That the pointers in the free list is "ordered"

  - That the free list and used list exactly complement each other

  - That the compaction results in a free list without contiguous blocks

  - etc.
-/


abbrev Pointer := Nat

abbrev Size := Nat

abbrev Block := Pointer × Size

def Block.ptr (block : Block) : Pointer := block.1

def Block.size (block : Block) : Size := block.2

-- Past-the-end pointer
def Block.end (block : Block) : Pointer := block.ptr + block.size

abbrev Blocks := List Block

structure Allocator where
  freeList : Blocks := [(0, 2^16)] -- sorted by first argument (ptr)
  usedList : Blocks := [] -- could/should we use a HashMap instead?
deriving Repr

-- The returned Nat refers the pointer.
def Allocator.alloc₀ (allocator : Allocator) (size: Nat) : Option (Nat × Allocator) := do
  if size == 0 then
    return (0, allocator) -- Any pointer would work for size 0
  let freeList := allocator.freeList
  guard !freeList.isEmpty
  let mut done : Blocks := []
  let mut todo : Blocks := freeList
  while !todo.isEmpty do
    let (ptr, currentSize) := List.head! todo
    if size <= currentSize then
      let newFreeBlocks : Blocks := if (size < currentSize) then
        -- chop the first free block on the left
        [(ptr + size, currentSize - size)]
      else
        [] -- perfect fit, remove the free block entirely
      let freeList := done ++ newFreeBlocks ++ todo.tail!
      let usedList := (ptr, size) :: allocator.usedList
      return (ptr, { allocator with freeList, usedList })
    else
      done := done ++ ([(ptr, currentSize)] : Blocks)
      todo := todo.tail!
  none -- failure

def findBlock (size: Size) (done_todo : Blocks × Blocks) : Blocks × Blocks :=
  let (done, todo) := done_todo
  match todo with
  | [] => (done, todo) -- failure
  | (ptr, currentSize) :: rest =>
    if size <= currentSize then
      (done, todo) -- found a suitable block
    else
      findBlock size (done ++ [(ptr, currentSize)], rest)
  termination_by
    done_todo.2.length -- That was surprisingly easy!

def Allocator.alloc₁ (allocator : Allocator) (size: Size) : Option (Pointer × Allocator) :=
  if size == 0 then
    (0, allocator) -- No allocation needed for size 0, return any pointer
  else
    let (done, todo) := findBlock size ([], allocator.freeList)
    match (done, todo) with
    | (_, []) => none -- failure
    | (done, (ptr, currentSize) :: rest) =>
      let newFreeBlocks : Blocks := if (size < currentSize) then
          -- chop the first free block on the left
          [(ptr + size, currentSize - size)]
      else
          [] -- perfect fit, remove the free block entirely
      let freeList := done ++ newFreeBlocks ++ rest
      let usedList := (ptr, size) :: allocator.usedList
      some (ptr, { allocator with freeList, usedList })

def Allocator.alloc := Allocator.alloc₁

#eval do
  let allocator : Allocator := {}
  let (ptr₁, allocator) <- allocator.alloc 512
  let (ptr₂, allocator) <- allocator.alloc 1024
  let (ptr₃, allocator) <- allocator.alloc 0
  let (ptr₄, allocator) <- allocator.alloc 1024
  return ([ptr₁, ptr₂, ptr₃, ptr₄], allocator)
-- some (
--   [0, 512, 0, 1536],
--   {
--     freeList := [(2560, 62976)],
--     usedList := [(1536, 1024), (512, 1024), (0, 512)]
--   })

-- Step 2: Freeing memory
partial def Allocator.free (allocator : Allocator) (ptr: Pointer) : Option Allocator := do
  let freeList := allocator.freeList
  let usedList := allocator.usedList
  let block <- usedList.find? (·.1 == ptr)
  let usedList := usedList.filter (· != block)
  let freeList := (block :: freeList) |>.mergeSort (·.1 < ·.1)
  return { allocator with freeList, usedList }.compact


-- Later : reconsider "compaction" of free blocks.

-- -- Find the first free block in the memory large enough to contain the requested number of Bytes.
-- -- Return before, current and after blocks (maybe stupid, we could just do a List.find afterwards).
-- -- Dunno. Keep it like that ATM.
-- def Allocator.findFreeBlock (allocator : Allocator) (size: Size) : Option (Blocks × Block × Blocks) := do
--   let freeList := allocator.freeList
--   guard !freeList.isEmpty
--   let mut before : Blocks := []
--   let mut current_and_after : Blocks := freeList
--   while !current_and_after.isEmpty do
--     let (ptr, freeSize) := current_and_after.head!
--     if size <= freeSize then
--       return (before.reverse, current_and_after.head!, current_and_after.tail!)
--     else
--       before := (ptr, freeSize) :: before
--       current_and_after := current_and_after.tail!
--   none -- failure

-- def Allocator.alloc (allocator : Allocator) (size: Size) : Option (Pointer × Allocator) := do
--   if size == 0 then
--     return (0, allocator) -- No allocation needed for size 0
--   let (before, current, after) <- findFreeBlock allocator size
--   let (ptr, freeSize) := current
--   let newFreeBlocks := if (size < freeSize) then
--     -- chop the first free block on the left
--     [(ptr + size.toUInt16, freeSize - size)]
--   else
--     [] -- perfect fit, remove the free block entirely
--   let freeList := before ++ newFreeBlocks ++ after
--   let usedList := (ptr, size) :: allocator.usedList
--   return (ptr, { allocator with freeList, usedList })


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
