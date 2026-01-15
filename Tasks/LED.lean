def LED (symbol : String := "🔵") (ms : UInt32 := 1000) : IO Unit := do
  repeat
    IO.println symbol
    IO.sleep ms

def main : IO Unit := do
  let _ <- IO.asTask <| LED "⚪" 1000
  let _ <- IO.asTask <| LED "⚫" 500
