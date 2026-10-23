
def f (m n : Nat) : Nat :=
  let p := m + n
  let q := 2 * p + 1
  p + q

#eval f 4 5 -- 28

def g (m n : Nat) : Nat :=
  (
    let p := m + n  -- or ";" instead of newline
    (
      let q := 2 * p + 1
      p + q
    )
  )

#eval (let n := 42 ; n + 1)

#eval g 4 5 -- 28

def h (m n : Nat) : Nat :=
  (fun p =>
    (let q := 2 * p + 1 ; p + q)
  ) (p := m + n)

def i (m n : Nat) : Nat :=
  (fun p =>
    (fun q => p + q) (q := 2 * p + 1)
  ) (p := m + n)

def k (m n : Nat) : Nat :=
  (fun p =>
    (fun q => p + q) (q := 2 * p + 1)
  ) (p := m + n)

#eval k 4 5 -- 28
