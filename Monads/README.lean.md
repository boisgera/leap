

Practical:
  - [ ] The `IO` monad, sequencing, `do` blocks, `←` and `return` (example).
  - [ ] `for`, `while`, `repeat`, `break`, `continue` and mutable variables.
  - [ ] Fibonacci : the naive FP version and the efficient one.
  - [ ] The second version, rewritten in `IO`.
  - [ ] The second version, rewritten in `Id`. `Id α = α` and `Id.run`.
  - [ ] Counting the number of recursive calls in the naive version:
        fib in `ℕ → ℕ → ℕ × ℕ` (args: `n` and `count`).
  - [ ] The `StateM ℕ` monad. `StateM ℕ = (ℕ → ℕ × ℕ)`; rewrite the
        signature of fib (not the implementation).
        Show the invocation as a fun call, `run` and `run'`.
  - [ ] Semantics of sequencing, `←` and `return` in `StateM σ`.
        Rewrite fib in a do block using that (and only that)
        (which means that we have to perform "manually" the +1 on
        the state).
  - [ ] get, set, modify, rewrite partially.
  - [ ] write a `Option ℕ` valued version of (the naive) fib, that
        chokes whenever an intermediate computation is > 255.
        No sugar initially, nested match stuff happen.
  - [ ] semantics of `return`, `<-` and sequencing. Adapt the impl above
        with a do block. Introduce `failure`.
  - [ ] Combine both sugary version in `StateT ℕ Option`.
        Pure magic, it works out of the box!

Theory:
  - [ ] pure, bind (>>=), signature. Diagram!
  - [ ] relate pure to `return` : return = pure + short-circuit + implicit `return unit`),
  - [ ] relate `<-` and sequencing (`bind` IS `<-` + sequ. with a no escape guarantee).
  - [ ] desugar printing the timestamp and returning 0?
  - [ ] explicit their semantics for `Id`, `State` and `Option`.
  - [ ] monadic laws.




