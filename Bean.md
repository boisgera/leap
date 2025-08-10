# Bean: Beam for Lean, the Actor model

Design v0:

  - Every actor has a single blocking input channel.
  - Every actor has a single non-blocking output channel.
  - Messages are made of JSON (or similar common type)

  - Actor is basically a state monade whose input is a message and
    state is internal state \times output channel.

  - Actor can "send" to its output channel, which is a
    non-blocking operation.

  - Orchestrator can spawn actors, which returns a PID.

  - Actors cannot spawn? That would be disappointing ... They need to be
    able to target a special actor, the orchestrator ... and that needs to
    be async, otherwise we would mutate the orchestrator's state.

  - Can the orchestrator be an actor itself? MMm need to distinguish
   event/queue/scheduler and orchestrator? 

  - Would probably be educational to have only the orchestrator able to
    spawn actors to be begin, in order to learn more about the design
    space.
