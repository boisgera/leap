
import Std

structure Function where
  fn : Float -> Float
  fn': Thunk Function

abbrev Registry := Std.HashMap String Function

def createRegistry : Registry := Id.run do {
  let mut registry : Registry := Registry.empty

  let value : Function := { fn := Float.exp, fn' := Thunk.mk fun () => registry.get! "exp"}
  -- registry := 44
  return registry
}
