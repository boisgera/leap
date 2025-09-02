def divideByTwo (n : Nat) : Nat :=
  if n % 2 == 0 then
    n / 2
  else
    sorry

#eval! divideByTwo 8

def main :=
  let _ := divideByTwo 8
  IO.println "Yep."

#eval! main
