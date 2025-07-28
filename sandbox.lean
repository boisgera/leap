

structure MyType where
  val : Nat
  deriving Inhabited, Repr

def myFunction : MyType :=
  panic! "This function is not implemented yet!"

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'
  deriving Inhabited, Repr

#eval Nat'.zero
#eval Nat'.succ Nat'.zero

#eval (default : Empty)
