import Std
open Std (HashMap)

inductive T where
|  string : String -> T
|  array : List T -> T
|  object : HashMap.Raw String T -> T
