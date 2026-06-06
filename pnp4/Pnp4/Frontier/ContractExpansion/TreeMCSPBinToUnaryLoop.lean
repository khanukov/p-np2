import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroRoute
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryBody
import Pnp4.Frontier.ContractExpansion.TreeMCSPLoopUntilSink

/-!
# `binToUnaryLoop` — the binary→unary loop (NP-verifier track — D2t-3 `ε`, scaffolding)

The D2t-3 converter loop (`TM_VERIFIER_STRATEGY.md` §12, sub-brick `ε`): repeat the one-pass body while
the counter `B > 0`, halting at `B = 0`.  This module assembles the loop **structure** from the pieces
proved earlier in D2t-3, via the established combinators (no new program machinery):

* `binToUnaryRouteBody` — `bZeroRouteProgram` (the proven routing decision: scan-stop → read → branch,
  phase `4` = `B=0`, phase `5` = `B>0`) with its **`acceptPhase` set to `5`** (the `B>0` target), so that
  `seq` redirects the `B>0` branch into the body and leaves the `B=0` branch (phase `4`) as a terminal
  phase;
* `binToUnaryLoopBody := seq binToUnaryRouteBody binToUnaryBody` — route first; on `B>0` (phase `5` =
  accept) hand off into the parallel session's `binToUnaryBody` (decrement + append + return to HOME,
  reaching its `idleCS` accept at composed phase `20`); on `B=0` rest at phase `4`;
* `binToUnaryLoop := loopUntilSink binToUnaryLoopBody ⟨4⟩` — re-enter the body on its accept (phase `20`,
  a completed `B>0` pass) and **halt at the sink phase `4`** (`B = 0`).

This brick ships the **definitions + phase-count facts** (the loop object and its shape).  The run
behaviour — discharging `loopUntilSink_reachesSink`'s `hbase` (`B=0` → sink, by lifting the run-through
`bZeroRouteProgram_runConfig_decide_true` through the outer `seq`) and `hstep` (`B>0` → re-enter with
`counterValue B` decreasing, via `binToUnaryBody`'s one-pass measure-decrease) — is the substantial
follow-up, then the `ζ` bridge `|U| = value(B)`.

**Progress classification (AGENTS.md): Infrastructure** — the loop assembly toward the NP-membership leg;
it proves no run behaviour and no separation here.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The routing decision (`bZeroRouteProgram`) re-pointed so its **accept phase is `5`** (the `B > 0`
target).  Under `seq` this routes `B > 0` into the body and leaves `B = 0` (phase `4`) terminal. -/
def binToUnaryRouteBody : ConstStatePhasedProgram Unit :=
  { bZeroRouteProgram with acceptPhase := ⟨5, by decide⟩ }

@[simp] theorem binToUnaryRouteBody_numPhases : binToUnaryRouteBody.numPhases = 6 := rfl

@[simp] theorem binToUnaryRouteBody_acceptPhase : (binToUnaryRouteBody.acceptPhase : Nat) = 5 := rfl

/-- The loop body: route, then on `B > 0` run one pass of `binToUnaryBody`. -/
def binToUnaryLoopBody : ConstStatePhasedProgram Unit :=
  seq binToUnaryRouteBody binToUnaryBody

@[simp] theorem binToUnaryLoopBody_numPhases : binToUnaryLoopBody.numPhases = 21 := rfl

/-- The binary→unary loop: re-enter the body on its accept (a completed `B > 0` pass), halt at the sink
phase `4` (`B = 0`). -/
def binToUnaryLoop : ConstStatePhasedProgram Unit :=
  loopUntilSink binToUnaryLoopBody ⟨4, by decide⟩

@[simp] theorem binToUnaryLoop_numPhases : binToUnaryLoop.numPhases = 21 := rfl

@[simp] theorem binToUnaryLoop_acceptPhase : (binToUnaryLoop.acceptPhase : Nat) = 4 := rfl

end ContractExpansion
end Frontier
end Pnp4
