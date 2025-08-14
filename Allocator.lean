-- Linear Memory Allocation

/-
Note: many interesting properties that we could prove here:

  - That the pointers in the free list is "ordered"

  - That the free list and used list exactly complement each other

  - That the compaction results in a free list without contiguous blocks

  - etc.
-/
open Classical

abbrev Pointer := Nat

abbrev Size := Nat

abbrev Block := Pointer × Size

def Block.ptr (block : Block) : Pointer := block.1

def Block.size (block : Block) : Size := block.2

-- Past-the-end pointer
def Block.end (block : Block) : Pointer := block.ptr + block.size

abbrev Blocks := List Block

structure Allocator where
  freeList : Blocks -- sorted by first argument (ptr)
  usedList : Blocks := [] -- could/should we use a HashMap instead?
deriving Repr

def Allocator.empty (size: Size) : Allocator :=
  { freeList := if size == 0 then [] else [(0, size)] }

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
    done_todo.2.length

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
      let usedList := allocator.usedList ++ [(ptr, size)]
      some (ptr, { allocator with freeList, usedList })

def Allocator.alloc := Allocator.alloc₁

-- TODO: split this test in several smaller ones.
#eval do
  let allocator := Allocator.empty 8
  let (_, allocator) <- allocator.alloc 0
  let (ptr₁, allocator) <- allocator.alloc 1
  let (ptr₂, allocator) <- allocator.alloc 2
  let (_, allocator) <- allocator.alloc 0
  let (ptr₃, allocator) <- allocator.alloc 3
  return ([ptr₁, ptr₂, ptr₃], allocator)
-- some ([0, 1, 3], { freeList := [(6, 2)], usedList := [(0, 1), (1, 2), (3, 3)] })

#eval do
  let allocator := Allocator.empty 8
  let (ptr, allocator) <- allocator.alloc 9
  return (ptr, allocator)
-- none

-- Step 2: Freeing memory
partial def Allocator.free (allocator : Allocator) (ptr: Pointer) : Option Allocator := do
  let freeList := allocator.freeList
  let usedList := allocator.usedList
  let block <- usedList.find? (·.1 == ptr)
  let usedList := usedList.filter (· != block)
  let freeList := (block :: freeList) |>.mergeSort (·.1 < ·.1)
  return { allocator with freeList, usedList } -- no compaction yet

-- TODO: (Arena-like properties) prove that:
-- 0. 1 allocation of size 0 always succeeds (not matter what the state if the alloc is)
-- 1. 1 allocation of total size <= available size (from empty) succeeds
-- 2. several allocations of total size <= available size succeed
-- 3. you can request largest spot and use it to guess if your alloc will
--    succeed
-- Other: show that for any sequence of non-zero allocs,
-- all the pointers are distinct?

theorem alloc_zero_succeeds : ∀ (allocator : Allocator), (allocator.alloc 0).isSome := by
  simp [Allocator.alloc, Allocator.alloc₁]

theorem alloc_one_succeeds_if_available :
  ∀ (asked available : Size),
  asked <= available ->
  (Allocator.empty available |>.alloc asked |>.isSome) := by
  intros asked available asked_le_available
  simp [Allocator.alloc, Allocator.alloc₁]
  -- TODO: cases on asked = 0 and asked > 0, simplify
  cases (em (asked = 0)) with -- That's a hammer here.
  | inl asked_zero => simp [asked_zero]
  | inr asked_pos =>
    simp [asked_pos]
    simp [Allocator.empty]
    cases (em (available = 0)) with
    | inl available_eq_zero =>
      rw [available_eq_zero] at asked_le_available
      rw [Nat.le_zero] at asked_le_available
      contradiction
    | inr available_pos =>
      simp [available_pos]
      simp [findBlock]
      simp [asked_le_available]

/-
Challenges for 2. :
  - need a way to express chained allocations first
  - proof uses structural induction on the list of sizes
-/

-- TODO: use mapM? declare the function as the appropriate StateT monad first?
def Allocator.chainAlloc₀ (sizes : List Size) (allocator : Allocator) : Option (List Pointer × Allocator) := do
  let mut pointers : List Pointer := []
  let mut currentAllocator := allocator
  for size in sizes do
    match currentAllocator.alloc size with
    | none => none -- failure
    | some (pointer, newAllocator) =>
      pointers := pointers ++ [pointer]
      currentAllocator := newAllocator
  return (pointers, currentAllocator)

abbrev Allocation := StateT Allocator Option -- Any op that requires an alloc that may fail

def Allocator.chainAlloc₁ (sizes : List Size) : Allocation (List Pointer) := do
  let mut pointers : List Pointer := []
  for size in sizes do
    let allocation := (Allocator.alloc (size := size))
    pointers := pointers ++ [<- allocation]
  return pointers

def Allocator.chainAlloc₂ (sizes : List Size) : Allocation (List Pointer) :=
  let sizeToAlloc := fun (size : Size) => Allocator.alloc (size := size)
  sizes.mapM sizeToAlloc

def Allocator.chainAlloc := Allocator.chainAlloc₂

theorem alloc_several_succeed_if_available :
  ∀ (sizes : List Size), ∀ (available : Size),
  sizes.sum <= available ->
  (Allocator.empty available |>.chainAlloc sizes |>.isSome) := by
  admit


-- TODO: Beyond Arena : Freeing memory:
-- 1. if you free some memory and allocate as many times 1 byte as needed,
--    you end up using all this memory again (before you fail).
--    More abstractly, show that there is a pattern of alloc that can use
--    any byte in the region?

#eval do
  let allocator := Allocator.empty 8
  let (ptr₁, allocator) <- allocator.alloc 1
  let (ptr₂, allocator) <- allocator.alloc 2
  let (_, allocator) <- allocator.alloc 3
  let allocator <- allocator.free ptr₁
  let allocator <- allocator.free ptr₂
  return allocator
-- some { freeList := [(0, 1), (1, 2), (6, 2)], usedList := [(3, 3)] }

-- Later : reconsider "compaction" of free blocks.


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
