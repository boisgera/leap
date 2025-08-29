def worldIcons := ["🌍", "🌎", "🌏"]

def main (args : List String) : IO Unit := do
  let mut name := ""
  let mut icon := ""
  if args.length == 0 then
    name := "world"
    let i <- IO.rand 0 2
    icon := worldIcons[i]!
  else
    name := args[0]!
    icon := "👋"
  IO.println s!"Hello {name}! {icon}"
