import Std.Sync.Channel

/-!
Note: `send` and `recv` are BOTH non-blocking and return a task that completes
when the transmission occurs. This is nice! The most common usage (Erlangish)
pattern would probably to:
  - send and "forget about it" (don't block and don't ever check for the
    transmission, that is buffering or recv, of the message).
  - recv and block immediately to get the value.
AAAAAAH: by casting the channel to Channel.Sync (a no-op), one can get the
sync version of the send and/or recv, with a different signature (no Task
wrapper). Or can unlock the synchronous API by casting to Std.Channel.Sync
(this is implicit) or when needed, calling the methods on `channel.sync`
rather than `channel`. Any of theses two idioms is probably better than
combining manually the receive and the get on the task to get a synchronous
recv.

Note:

  - Go is synchronous for sends and receives and does not have unlimited buffers
    (a very back-pressure friendly configuration) and especially a very nice
    way to use channels as synch mechanisms instead of locks, events, etc.
  - Erlang is asynchronous for sends and synchronous for receives and has only
    truly unlimited buffers (except of course that we can emulate a sync call on
    top of an async one with an ack).

I see very limited use cases for asynchronous reads (?).

-/

partial def ping (input : Std.Channel.Sync Nat) (output : Std.Channel Nat) : IO Unit := do
  let count <- input.recv
  IO.println s!"ping {count}"
  IO.sleep 3000
  _ <- output.send (count + 1)
  ping input output

partial def pong (input : Std.Channel.Sync Nat) (output : Std.Channel Nat) : IO Unit := do
  let count <- input.recv
  IO.println s!"pong {count}"
  IO.sleep 3000
  _ <- output.send (count + 1)
  ping input output

def main : IO Unit := do
  let c_1 <- Std.Channel.new (α := Nat) (capacity := some 0)
  let c_2 <- Std.Channel.new (α := Nat) (capacity := some 0)
  _ <- IO.asTask <| ping (input := c_1) (output := c_2)
  _ <- IO.asTask <| pong (input := c_2) (output := c_1)
  _ <- c_1.send 0
