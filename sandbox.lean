
def roll : Nat :=
  sorry

#check roll
-- roll: Nat

#check IO.rand
-- IO.rand (lo hi : Nat) : BaseIO Nat

def rollDice := IO.rand 1 6

#check rollDice
-- rollDice : BaseIO Nat

#eval rollDice
-- 1

#eval rollDice
-- 4

def unit : Unit := ()

#check unit
-- unit : Unit

#eval unit == ()
-- true

def messageToUnit (s : String) : Unit :=
  let _ := s -- we have to "use" s.
  ()

#check messageToUnit "Hello world! 👋"
-- messageToUnit "Hello world! 👋"

#eval messageToUnit "Hello world! 👋" == ()
-- true

#check IO.println (α := String)
-- IO.println : String → IO Unit

def hello := IO.println "Hello world! 👋"

#check hello
-- hello : IO Unit

#eval hello
-- Hello world! 👋
