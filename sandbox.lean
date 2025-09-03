
#check IO.rand
-- IO.rand (lo hi : Nat) : BaseIO Nat

#eval IO.rand 1 6
-- 4

#eval IO.rand 1 6
-- 2

-- `BaseIO` is the simplest IO monad of Lean. Actions of this type can have
-- side-effects in the real world but cannot fail.

#check BaseIO
-- BaseIO : Type → Type

#print BaseIO
-- def BaseIO : Type → Type := EIO Empty

#check EIO
-- EIO (ε : Type) : Type → Type

#print EIO
-- def EIO : Type → Type → Type := fun ε => EStateM ε IO.RealWorld


#print IO.RealWorld
-- def IO.RealWorld : Type := Unit

-- EStateM is a combined state and exception monad.
#check EStateM
-- EStateM.{u} (ε σ α : Type u) : Type u

-- The state is of type σ and each action produces a. Every state transition
-- produces a new state and:
--   - either an ok result that boxes a value of type α
--   - or an error result that boxes an error info of type ε
#print EStateM.Result
-- inductive EStateM.Result.{u} : Type u → Type u → Type u → Type u
-- number of parameters: 3
-- constructors:
-- EStateM.Result.ok : {ε σ α : Type u} → α → σ → EStateM.Result ε σ α
-- EStateM.Result.error : {ε σ α : Type u} → ε → σ → EStateM.Result ε σ α

-- For `BaseIO` actions,
--   - The state σ is IO.RealWorld defined as Unit. So there is no
--     associated state *managed by Lean* (the state is entirely external:
--     the info that you have changed on your hard drive, in the cloud, etc.)
--   - The error type is `Empty` which has no element: the action cannot fail.

#eval IO.println "Hello world!"
-- Hello world!

#check IO.println
-- {α : Type u_1} → [ToString α] → α → IO Unit

-- The `IO` monad is probably more common. Actions of this type can have
-- side-effects in the real world and can fail.

#check IO
-- IO : Type -> Type

#print IO
-- @[reducible] def IO : Type → Type := EIO IO.Error

-- There is a (long) list of possible errors, described by the `IO.Error` type.

#check IO.Error
-- IO.Error : Type

#print IO.Error
-- inductive IO.Error : Type
-- number of parameters: 0
-- constructors:
-- IO.Error.alreadyExists : Option String → UInt32 → String → IO.Error
-- IO.Error.otherError : UInt32 → String → IO.Error
-- IO.Error.resourceBusy : UInt32 → String → IO.Error
-- IO.Error.resourceVanished : UInt32 → String → IO.Error
-- IO.Error.unsupportedOperation : UInt32 → String → IO.Error
-- IO.Error.hardwareFault : UInt32 → String → IO.Error
-- IO.Error.unsatisfiedConstraints : UInt32 → String → IO.Error
-- IO.Error.illegalOperation : UInt32 → String → IO.Error
-- IO.Error.protocolError : UInt32 → String → IO.Error
-- IO.Error.timeExpired : UInt32 → String → IO.Error
-- IO.Error.interrupted : String → UInt32 → String → IO.Error
-- IO.Error.noFileOrDirectory : String → UInt32 → String → IO.Error
-- IO.Error.invalidArgument : Option String → UInt32 → String → IO.Error
-- IO.Error.permissionDenied : Option String → UInt32 → String → IO.Error
-- IO.Error.resourceExhausted : Option String → UInt32 → String → IO.Error
-- IO.Error.inappropriateType : Option String → UInt32 → String → IO.Error
-- IO.Error.noSuchThing : Option String → UInt32 → String → IO.Error
-- IO.Error.unexpectedEof : IO.Error
-- IO.Error.userError : String → IO.Error

def printlnOrPanic! {α} [ToString α] (a : α) : IO Unit := do
  try
    IO.println a
  catch error => -- catch every error
    panic! s!"😱 {error}"

def printlnOrPanicIfPermissionDenied! {α} [ToString α] (a : α) : IO Unit := do
  try
    IO.println a
  catch e =>
    match e with
    | .permissionDenied _ _ _ => panic! s!"🔒 Permision denied"
    | _ => return -- This is fine.

def printlnOrPanicIfPermissionDenied!' {α} [ToString α] (a : α) : IO Unit := do
  try
    IO.println a
  catch
  | .permissionDenied _ _ _ => panic! s!"🔒 Permision denied"
  | _ => return -- This is fine.


-- Actions of type `BaseIO` are automatically promoted to the `IO` type
-- when needed.

def printDie : IO Unit := do
  let die <- IO.rand 1 6
  IO.println s!"🎲 {die}"

#eval printDie
-- 🎲 5
