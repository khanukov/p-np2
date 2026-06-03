import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

/-!
# Self-terminating body-reentry loop combinator (NP-verifier track — head-advancing control)

`repeatBody` (`TreeMCSPRepeatBody.lean`) loops a body a counter-determined number of times, but its decide
phase consumes a counter tick **at the head** and moves **left** each pass — so its body must leave the
head fixed.  The record-stream decoder (D2) and the gate interpreter (I1) instead loop a body that
**advances the head right** (e.g. `gateOneRecordDecoder` walks past one record), so they need a different
control structure.

`loopUntilSink B sink` is that structure: it runs `B`, and
* when `B` reaches its **accept** phase (a unit of work finished, head advanced), it **re-enters** `B` at
  its start phase — the head-advancing back-edge;
* when `B` reaches a designated **sink** phase, it **halts**.

For the stream decoder this is exactly right: `gateOneRecordDecoder`'s accept phase (`12`) means "decoded
one record, head at the next record" → loop; its malformed sink (`13`), reached on a `1^5` tag, doubles
as the **end-of-stream marker** → halt.  No separate counter or leftward scan-back is needed; termination
is data-driven by the sink.

This brick ships the combinator **definition** and its **single-step / structural** lemmas (the back-edge
and halt transitions, the body pass-through, and `neverMovesLeft` inherited from `B`).  Following the
toolkit's pattern (`seq`/`repeatBody` shipped single-step lemmas before run-invariants), the run-through
("`B` runs to accept then re-enters") and the run-`K`-records correctness are the documented follow-up.

**Progress classification (AGENTS.md): Infrastructure** — control toolkit toward the NP-membership leg;
it builds no verifier and proves no separation.  All surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- Self-terminating body-reentry loop: re-enter `B` at its start phase whenever it reaches its accept
phase (the head-advancing back-edge); halt when it reaches the `sink` phase.  Reuses `B`'s phases (the
back-edge target `B.startPhase` is an existing phase), so `numPhases = B.numPhases`. -/
def loopUntilSink (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases) :
    ConstStatePhasedProgram Unit where
  numPhases := B.numPhases
  startPhase := B.startPhase
  startState := ()
  acceptPhase := sink
  acceptState := ()
  transition := fun i _ b =>
    if i = B.acceptPhase then (B.startPhase, (), b, Move.stay)
    else if i = sink then (sink, (), b, Move.stay)
    else B.transition i () b
  timeBound := fun n => n

@[simp] theorem loopUntilSink_numPhases (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases) :
    (loopUntilSink B sink).numPhases = B.numPhases := rfl

@[simp] theorem loopUntilSink_startPhase (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases) :
    (loopUntilSink B sink).startPhase = B.startPhase := rfl

@[simp] theorem loopUntilSink_acceptPhase (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases) :
    (loopUntilSink B sink).acceptPhase = sink := rfl

@[simp] theorem loopUntilSink_timeBound (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    (n : Nat) : (loopUntilSink B sink).timeBound n = n := rfl

/-! ### Transition characterization (the back-edge, the halt, the body pass-through) -/

/-- **Back-edge.** At `B`'s accept phase the loop jumps to `B`'s start phase (head unchanged) — the
re-entry that makes the loop head-advancing. -/
theorem loopUntilSink_transition_loop (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    (s : Unit) (b : Bool) :
    (loopUntilSink B sink).transition B.acceptPhase s b = (B.startPhase, (), b, Move.stay) := by
  simp [loopUntilSink]

/-- **Halt.** At the `sink` phase the loop idles (the loop's accept phase). -/
theorem loopUntilSink_transition_halt (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    (hne : sink ≠ B.acceptPhase) (s : Unit) (b : Bool) :
    (loopUntilSink B sink).transition sink s b = (sink, (), b, Move.stay) := by
  simp [loopUntilSink, hne]

/-- **Body pass-through.** Away from the accept and sink phases, the loop runs `B`'s transition verbatim
— so `B`'s own run behaviour transfers between back-edges. -/
theorem loopUntilSink_transition_body (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    {i : Fin B.numPhases} (h1 : i ≠ B.acceptPhase) (h2 : i ≠ sink) (s : Unit) (b : Bool) :
    (loopUntilSink B sink).transition i s b = B.transition i () b := by
  simp [loopUntilSink, h1, h2]

/-- If `B` never moves the head left, neither does the loop (the control steps idle; the body steps are
`B`'s). -/
theorem loopUntilSink_transition_move (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    (hB : ∀ (i : Fin B.numPhases) (s : Unit) (b : Bool), (B.transition i s b).2.2.2 ≠ Move.left)
    (i : Fin B.numPhases) (s : Unit) (b : Bool) :
    ((loopUntilSink B sink).transition i s b).2.2.2 ≠ Move.left := by
  unfold loopUntilSink
  dsimp only
  split_ifs
  · simp
  · simp
  · exact hB i () b

theorem loopUntilSink_neverMovesLeft (B : ConstStatePhasedProgram Unit) (sink : Fin B.numPhases)
    (hB : ∀ (i : Fin B.numPhases) (s : Unit) (b : Bool), (B.transition i s b).2.2.2 ≠ Move.left) :
    TMNeverMovesLeft ((loopUntilSink B sink).toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact loopUntilSink_transition_move B sink hB i s b

end ContractExpansion
end Frontier
end Pnp4
